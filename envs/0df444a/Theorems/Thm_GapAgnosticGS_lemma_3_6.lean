-- Prove2me | Theorems.Thm_GapAgnosticGS_lemma_3_6
-- name    : GapAgnosticGS.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:55.799077+00:00
-- url     : https://prove2.me/theorems/1b4f19d5-5115-4d83-adc1-5253e4a482f6
-- title:
--   Lemma 3.6 (= Lemma A.2) — the variable-time threshold test accepts high branches and rejects low ones
-- statement:
--   Let $E$ be a hidden-basis environment, $0\le\ell_2<\ell_1\le1$, $\Delta=\ell_1-\ell_2$, $0<a<1/4$ and $m=\lceil\log_2(1/\Delta)\rceil+2$. Let $\mathrm{GTT}(\eta,a;\tau)$, for $\eta\in(0,1/2)$ and $\tau\in[0,1]$, be gapped threshold tests for $E$ (the guarantee of Lemma 3.5). Run Algorithm 2 (VGTT) on the branch $|\phi_j\rangle_I$. Then
--
--   1. if $p_j\ge\ell_1-\Delta/8$, the component of the output with $F=1$ has norm at least $\sqrt{1-ma^2}$;
--   2. if $p_j\le\ell_1-\Delta/2$, the component of the output with $F=0$ has norm at least $\sqrt{1-a^2}$.
--
--   Since Algorithm 2 acts only on $I$, this is the statement "VGTT applied to register $I$ of $|\Phi\rangle_{RI}$, conditioned on branch $j$". The flag $F$ separates the branches above and below the threshold window.
--
--   Differences from the source:
--   - reading: VGTT applied to register I of |Φ⟩_RI … condition on branch j → Algorithm 2 run on the input |ϕ_j⟩_I; reason: Algorithm 2 acts on I only, so the branch-j output is |ϕ_j*⟩_R times the output on |ϕ_j⟩_I
--   - generalization: Algorithm 2 built from the GTT of Lemma 3.5 → Algorithm 2 built from any family of unitaries gtt η τ satisfying Lemma 3.5's (i)–(ii) with error a for all η ∈ (0,1/2), τ ∈ [0,1]; reason: Lemma 3.5 gives the GTT only existentially; the statement specializes to it
--   - encoding: the amplitude of |1⟩_F (resp. |0⟩_F) → the norm of the output component with F = 1 (resp. F = 0); reason: same quantity
--   - encoding: registers (C_r, P_r), stages r = 1, …, m → one workspace type P for every stage, stages indexed 0, …, m − 1, m fixed by the hypothesis m = ⌈log₂(1/∆)⌉ + 2; reason: registers of different sizes can be padded; Lean indexing
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.6 (Variable-time threshold test), p.11 (PDF p.12); Lemma A.2 and Algorithm 2, p.27 (PDF p.28)

import Definitions.Def_GapAgnosticGS_IsGTT
import Definitions.Def_GapAgnosticGS_vgtt
import Definitions.Def_GapAgnosticGS_vgttInit
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.6 (Variable-time threshold test), p.11 (PDF p.12): "VGTT applied to register I
of |Φ⟩_RI outputs a state such that condition on branch j, if p_j ≥ ℓ1 − ∆/8, the amplitude of
|1⟩_F is at least √(1 − ma²), and if p_j ≤ ℓ1 − ∆/2, the amplitude of |0⟩_F is at least √(1 − a²)";
the same statement for Algorithm 2 is Lemma A.2, p.27 (PDF p.28), with Algorithm 2's
requirements "0 ≤ ℓ2 < ℓ1 ≤ 1; 0 < a < 1/4", "∆ ← ℓ1 − ℓ2", "m ← ⌈log2(1/∆)⌉ + 2".

For every environment and every family `gtt η τ` of gapped threshold tests with amplitude error
`a` (Lemma 3.5, `IsGTT`, for all `η ∈ (0,1/2)`, `τ ∈ [0,1]`), Algorithm 2 run on `|ϕ_j⟩_I`:
the `F = 1` component has norm at least `√(1 − m a²)` when `p_j ≥ ℓ₁ − ∆/8`, and the `F = 0`
component has norm at least `√(1 − a²)` when `p_j ≤ ℓ₁ − ∆/2`.

**Formalization Note.** "Condition on branch j" of `|Φ⟩_RI = n^{−1/2} Σ_j |ϕ_j^*⟩_R|ϕ_j⟩_I`
(Lemma 3.3): Algorithm 2 acts on `I` only, so the branch-`j` output is `|ϕ_j^*⟩_R` times the output
on input `|ϕ_j⟩_I`, which is what is stated. The lemma is stated for any implementation of the
tests of Lemma 3.5 (the GTT is only given existentially); all stages use one workspace type `P`
with zero state `p₀` (registers of different sizes can be padded). -/
theorem lemma_3_6 {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A} {Prj : Matrix A A ℂ}
    (Env : HidEnv n A a₀ Prj) {P : Type} [Fintype P] [DecidableEq P] (p₀ : P)
    (gtt : ℝ → ℝ → Matrix ((Fin n × A) × Bool × P) ((Fin n × A) × Bool × P) ℂ)
    (ℓ₁ ℓ₂ a : ℝ) (hℓ₂ : 0 ≤ ℓ₂) (hℓ : ℓ₂ < ℓ₁) (hℓ₁ : ℓ₁ ≤ 1) (ha : 0 < a) (ha' : a < 1 / 4)
    (hgtt : ∀ η τ, η ∈ Set.Ioo 0 (1 / 2) → τ ∈ Set.Icc 0 1 →
      IsGTT Env ((false, p₀) : Bool × P) Prod.fst (gtt η τ) η τ a)
    (m : ℕ) (hm : m = ⌈Real.logb 2 (1 / (ℓ₁ - ℓ₂))⌉₊ + 2) (j : Fin n) :
    let out := act (vgtt Env.E gtt m ℓ₁) (vgttInit m a₀ p₀ (Env.φ j))
    (ℓ₁ - (ℓ₁ - ℓ₂) / 8 ≤ reward Env j →
      Real.sqrt (1 - m * a ^ 2) ≤
        Real.sqrt (∑ x, if x.2.2.2 = true then ‖out x‖ ^ 2 else 0)) ∧
    (reward Env j ≤ ℓ₁ - (ℓ₁ - ℓ₂) / 2 →
      Real.sqrt (1 - a ^ 2) ≤
        Real.sqrt (∑ x, if x.2.2.2 = false then ‖out x‖ ^ 2 else 0)) := by sorry

end GapAgnosticGS
