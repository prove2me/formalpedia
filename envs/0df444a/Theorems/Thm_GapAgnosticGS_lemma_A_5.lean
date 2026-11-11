-- Prove2me | Theorems.Thm_GapAgnosticGS_lemma_A_5
-- name    : GapAgnosticGS.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:20.838234+00:00
-- url     : https://prove2.me/theorems/7905bf97-cc64-408c-86ee-4f9d6b2e6c11
-- title:
--   Lemma A.5 — stopping times of VGTT: $t_r=O(2^r\log\frac1a)$ and the weighted $t_{\rm avg}^2$ bound
-- statement:
--   For every constant $C_0>0$ there is $C_1>0$ (depending only on $C_0$) with the following property. Let $E$ be a hidden-basis environment, $0\le\ell_2<\ell_1\le1$, $\Delta=\ell_1-\ell_2$, $0<a<1/4$, $m=\lceil\log_2(1/\Delta)\rceil+2$, and let the stages of Algorithm 2 use gapped threshold tests (Lemma 3.5) with query counts at most $C_0\,\eta^{-1}\log(1/a)$. Let $t_r$ be the number of queries through stage $r$, and let $c_j$ be the amplitudes of a normalized input $|\Psi\rangle_{RI}=\sum_jc_j|\zeta_j\rangle_R|\phi_j\rangle_I$. Then
--
--   $$t_r\le C_1\,2^r\log\frac1a\ (r\le m),\qquad t_{\max}=t_m\le C_1\,\frac1\Delta\log\frac1a,$$
--
--   $$t_{\rm avg}^2=\sum_j|c_j|^2\sum_{r}\Pr\nolimits_j[\text{stop at }r]\,t_r^2\le C_1\Bigg(\sum_{j:\,p_j\ge\ell_1-\Delta/2}\frac{|c_j|^2}{\Delta^2}+\sum_{i:\,p_i<\ell_1-\Delta/2}\frac{|c_i|^2}{(\ell_1-p_i)^2}\Bigg)\log^2\frac1a .$$
--
--   Branches far below the threshold stop early; this is the source of the $\Gamma$-dependence of the final query bound.
--
--   Differences from the source:
--   - generalization: the GTT circuits of Lemma 3.5 inside Algorithm 2, with query complexity t_r → any family of gapped threshold tests with error a and any query-count assignment cost η τ ≤ C₀ (1/η) log(1/a); reason: Lemma 3.5 gives the tests and their O-bound only existentially; the statement specializes to them
--   - reading: O(·) → constants C₁ depending only on the constant C₀ of the tests' query bound, chosen before every other quantity; reason: the O-constant of Lemma 3.5 is the only data the bounds depend on
--   - reading: t²_avg for the input |Ψ⟩ with branch amplitudes c_j → Σ_j |c_j|² Σ_r Pr_j[stop at r] t_r², with Pr_j the explicit stopping law vgttStopProb of branch j; reason: Theorem A.4's t_avg = (Σ_r p_r t_r²)^{1/2}; Algorithm 2 acts on I only, so branch j of |Ψ⟩ stops with branch j's law
--   - encoding: t_r, the query complexity through stage r; t_max = max_r t_r → t_r = sum of the costs of the tests executed in stages 1, …, r (a skipped stage costs 0); t_max = t_m; reason: t_r is nondecreasing in r
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma A.5 (Stopping times of VGTT), p.29 (PDF p.30); input of p.28 (PDF p.29); Theorem A.4, Eq. (26), p.28 (PDF p.29)

import Definitions.Def_GapAgnosticGS_IsGTT
import Definitions.Def_GapAgnosticGS_vgttStopProb

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma A.5 (Stopping times of VGTT), p.29 (PDF p.30): "Let t_r be the query complexity
through stage r of Algorithm 2. Then t_r = O(2^r log(1/a)), t_max = O((1/∆) log(1/a)). Let c_j be
the amplitude of the initial state |Ψ⟩ on branch j. Then
t²_avg = O((Σ_{j:p_j≥ℓ1−∆/2} |c_j|²/∆² + Σ_{i:p_i<ℓ1−∆/2} |c_i|²/(ℓ1 − p_i)²) log²(1/a))";
with p.28 (PDF p.29): "Let |Ψ⟩_RI = Σ_j c_j|ζ_j⟩_R|ϕ_j⟩_I be a normalized input … R may be
trivial", and Theorem A.4, Eq. (26): "t_avg := √(Σ_r p_r t_r²)".

For every constant `C₀` bounding the tests' query counts as in Lemma 3.5 there is `C₁` (depending
only on `C₀`) such that, for every environment, every family of gapped threshold tests `gtt` with
error `a` whose query counts `cost η τ` satisfy `cost η τ ≤ C₀ (1/η) log(1/a)`, and every
normalized amplitude vector `c`: (1) `t_r ≤ C₁ 2^r log(1/a)` for `r ≤ m`; (2) `t_m ≤ C₁ ∆^{−1}
log(1/a)`; (3) `Σ_j |c_j|² Σ_r Pr_j[stop at r] t_r² ≤ C₁ (…) log²(1/a)`.

**Formalization Note.** `t_r` (through paper stage `r`) is the sum of the query counts of the tests
executed in stages `1, …, r` (a skipped stage costs `0`); `t_max = t_m`. The stopping law of branch
`j` is `vgttStopProb` (the branch stops at the stage whose flag is first set, or at the last
stage). `t²_avg` is the branch-weighted mean `Σ_j |c_j|² Σ_r Pr_j[stop at r] t_r²` (Algorithm 2
acts on `I` only, so branch `j` of `|Ψ⟩` stops with branch `j`'s law). O(·) is a constant `C₁`
depending only on the constant `C₀` of the tests. -/
theorem lemma_A_5 :
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A} {Prj : Matrix A A ℂ}
      (Env : HidEnv n A a₀ Prj) {P : Type} [Fintype P] [DecidableEq P] (p₀ : P)
      (gtt : ℝ → ℝ → Matrix ((Fin n × A) × Bool × P) ((Fin n × A) × Bool × P) ℂ)
      (cost : ℝ → ℝ → ℕ) (ℓ₁ ℓ₂ a : ℝ), 0 ≤ ℓ₂ → ℓ₂ < ℓ₁ → ℓ₁ ≤ 1 → 0 < a → a < 1 / 4 →
      (∀ η τ, η ∈ Set.Ioo 0 (1 / 2) → τ ∈ Set.Icc 0 1 →
        IsGTT Env ((false, p₀) : Bool × P) Prod.fst (gtt η τ) η τ a ∧
        (cost η τ : ℝ) ≤ C₀ * (1 / η) * Real.log (1 / a)) →
      ∀ (m : ℕ), m = ⌈Real.logb 2 (1 / (ℓ₁ - ℓ₂))⌉₊ + 2 →
      ∀ c : Fin n → ℂ, ∑ j, ‖c j‖ ^ 2 = 1 →
      let Δ := ℓ₁ - ℓ₂
      let t : ℕ → ℝ := fun r => ∑ i ∈ Finset.range r,
        if 0 ≤ ℓ₁ - 3 * (2 : ℝ)⁻¹ ^ (i + 1) / 2 then
          (cost ((2 : ℝ)⁻¹ ^ (i + 1) / 2) (ℓ₁ - 3 * (2 : ℝ)⁻¹ ^ (i + 1) / 2) : ℝ)
        else 0
      (∀ r, r ≤ m → t r ≤ C₁ * 2 ^ r * Real.log (1 / a)) ∧
      t m ≤ C₁ * (1 / Δ) * Real.log (1 / a) ∧
      ∑ j : Fin n, ‖c j‖ ^ 2 * ∑ r : Fin m, vgttStopProb Env gtt m ℓ₁ p₀ j r * t (r + 1) ^ 2 ≤
        C₁ * ((∑ j : Fin n, if ℓ₁ - Δ / 2 ≤ reward Env j then ‖c j‖ ^ 2 / Δ ^ 2
            else ‖c j‖ ^ 2 / (ℓ₁ - reward Env j) ^ 2) * Real.log (1 / a) ^ 2) := by sorry

end GapAgnosticGS
