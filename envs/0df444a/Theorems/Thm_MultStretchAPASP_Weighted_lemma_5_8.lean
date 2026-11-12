-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_lemma_5_8
-- name    : MultStretchAPASP.Weighted.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:11:10.22118+00:00
-- url     : https://prove2.me/theorems/99c4d771-691c-453e-8335-7eaad0b6382a
-- title:
--   Lemma 5.8 — Algorithm 9 on N^α × N^β and N^β × N^γ matrices runs in Õ(N^{ω(α,β,γ)+o(1)} log W_max)
-- statement:
--   Suppose $M_1$, $M_2$ have entries in $[W_{\max}]\cup\{\infty\}$ and dimensions $N^\alpha\times N^\beta$ and $N^\beta\times N^\gamma$ for some $N,\alpha,\beta,\gamma>0$, and let $\varepsilon>0$ be a fixed constant. Then Algorithm 9 runs in time
--   $$\tilde O\bigl(N^{\omega(\alpha,\beta,\gamma)+o(1)}\log W_{\max}\bigr).$$
--
--   Formally: for all $\alpha,\beta,\gamma>0$, $\varepsilon>0$ and $\eta>0$ there are a program and a constant $C$ such that for all $N\ge1$, $W_{\max}\ge1$, offsets $\mathrm{off}_1,\mathrm{off}_2$ and matrices as above whose entries are at least the offsets (Algorithm 9's input guarantee), the program halts on every random tape within $C(\log_2(N+2))^C N^{\omega(\alpha,\beta,\gamma)+\eta}L+C$ steps, $L=\log_2(W_{\max}+1)+1$, and outputs a possible output of $\textsc{Offset\_Shifted\_AMPMM}(M_1,M_2,\mathrm{off}_1,\mathrm{off}_2,\varepsilon)$. Lemma 5.12 uses it for the products of line 24 of Algorithm 10.
--
--   Differences from the source:
--
--   - reading: an algorithm with a running time (the paper names no machine model) → a program of the published randomized word RAM DynConnWC.Program with the run notions of MinKCutII_Main_Runs, words of wordSize C inp T = C·⌈log₂(|inp| + Σ inp + 2 + ⌈T⌉)⌉ bits, input read once in order, output written as words; reason: a standard unit-cost word RAM with Θ(log)-bit words; the same machine defines ω(a, b, c), so the exponents in the bounds and the machine agree
--   - reading: Algorithm 9 runs in time T → some program halts within T steps on every random tape and outputs a possible output of Algorithm 9 (IsOffsetShiftedOut); reason: Algorithm 9 calls a black box; its running time is that of an implementation, whose output must be one Algorithm 9 allows
--   - encoding: dimensions N^α × N^β, N^β × N^γ for some N > 0 → Fin ⌈N^α⌉ × Fin ⌈N^β⌉ and Fin ⌈N^β⌉ × Fin ⌈N^γ⌉ for a natural number N ≥ 1; reason: ω(α, β, γ) is defined through natural sizes; dimensions are rounded up
--   - encoding: entries in [W_max] ∪ {∞}, each at least the offset → entries in ℕ∞ with 1 ≤ entry ≤ Wmax or ⊤, natural offsets with off_i ≤ every entry, Wmax ≥ 1; input [r, s, t, Wmax, off₁, off₂] followed by both matrices in the two-word code; output in ℕ∞; reason: Algorithm 9's input guarantee; the shifts of Algorithm 10 are integers; ∞ needs an unambiguous code
--   - reading: ε > 0 a fixed constant; Õ(N^{ω(α,β,γ)+o(1)} log W_max) → for every ε > 0 and η > 0 a program and a constant C with time C·(log₂(N+2))^C·N^{ω(α,β,γ)+η}·(log₂(Wmax+1) + 1) + C; reason: constants may depend on the fixed ε; the o(1) as ∀ η; Õ with an explicit constant
--   - encoding: log W_max → log₂(W_max + 1) + 1; reason: equals log W_max up to a constant factor for W_max ≥ 2 and does not vanish at W_max = 1
--   - reading: ω(a, b, c): "the infimum over all τ > 0 such that, for every constant ε > 0, the product A·B can be computed in O(n^{τ+ε}) runtime" (p. 7), A ∈ ℝ^{n^a×n^b}, B ∈ ℝ^{n^b×n^c}; ω = ω(1, 1, 1) → omega3 a b c: the infimum of the τ > 0 achievable, for every ε > 0, by a deterministic program of the word RAM of DynConnWC_Program in C·N^{τ+ε} + C steps on natural-number matrices of sizes ⌈N^a⌉ × ⌈N^b⌉ and ⌈N^b⌉ × ⌈N^c⌉; omega = omega3 1 1 1; reason: the paper defines ω by running time and names no machine; a word RAM takes integer inputs; deterministic because Theorem 2.14 claims a deterministic algorithm in time n^{ω(1,r,1)+o(1)}; the same machine runs every algorithm of the mission
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 28, Lemma 5.8

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Encoding
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

set_option autoImplicit false

open scoped ENNReal
open DynConnWC MinKCutII.Main

namespace MultStretchAPASP.Weighted

/-- **Lemma 5.8** (p. 28). Let `α, β, γ > 0` and let `ε > 0` be fixed. For every `η > 0` (the
`o(1)`) there are a program (an implementation of Algorithm 9) and a constant `C` such that for all
`N ≥ 1`, `Wmax ≥ 1`, offsets `off₁, off₂` and matrices `M₁` (`⌈N^α⌉ × ⌈N^β⌉`) and `M₂`
(`⌈N^β⌉ × ⌈N^γ⌉`) with entries in `[Wmax] ∪ {∞}` and at least the offsets, on every random tape the
program halts within `C·(log₂(N+2))^C·N^{ω(α,β,γ)+η}·(log₂(Wmax+1) + 1) + C` steps and outputs a
possible output of `Offset_Shifted_AMPMM(M₁, M₂, off₁, off₂, ε)`. -/
theorem lemma_5_8 :
    ∀ α β γ : ℝ, 0 < α → 0 < β → 0 < γ → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∃ (P : Program) (C : ℕ),
        ∀ (N Wmax off₁ off₂ : ℕ) (M₁ : Fin (dimOf N α) → Fin (dimOf N β) → ℕ∞)
          (M₂ : Fin (dimOf N β) → Fin (dimOf N γ) → ℕ∞), 1 ≤ N → 1 ≤ Wmax →
          (∀ i k, (1 ≤ M₁ i k ∧ M₁ i k ≤ (Wmax : ℕ∞)) ∨ M₁ i k = ⊤) →
          (∀ k j, (1 ≤ M₂ k j ∧ M₂ k j ≤ (Wmax : ℕ∞)) ∨ M₂ k j = ⊤) →
          (∀ i k, (off₁ : ℕ∞) ≤ M₁ i k) → (∀ k j, (off₂ : ℕ∞) ≤ M₂ k j) →
          let T : ℝ := (C : ℝ) * polylog N C * ((N : ℝ) ^ (omega3 α β γ + η) * logW Wmax) + C
          let inp := minPlusInput Wmax off₁ off₂ M₁ M₂
          let W := wordSize C inp T
          ∀ ω : ℕ → Fin (2 ^ W), HaltsWithin W P inp ω T ∧
            ∃ M : Fin (dimOf N α) → Fin (dimOf N γ) → ℕ∞,
              finalOutput W P inp ω = rowsWords (List.finRange (dimOf N α)) M ∧
              IsOffsetShiftedOut ε Finset.univ Finset.univ Finset.univ
                (fun i k => (M₁ i k : ℝ≥0∞)) (fun k j => (M₂ k j : ℝ≥0∞))
                (off₁ : NNReal) (off₂ : NNReal) (fun i j => (M i j : ℝ≥0∞)) := by sorry

end MultStretchAPASP.Weighted
