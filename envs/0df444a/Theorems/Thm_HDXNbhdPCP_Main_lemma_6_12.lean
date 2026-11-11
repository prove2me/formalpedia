-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_lemma_6_12
-- name    : HDXNbhdPCP.Main.lemma_6_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:52.065399+00:00
-- url     : https://prove2.me/theorems/20306aa4-be40-4d2d-aad2-f55b4c0ce56c
-- title:
--   Lemma 6.12 — list decoding a sound neighbourhood test
-- statement:
--   Let $X$ be a weighted 3-partite $\lambda$-product complex ($0\le\lambda\le1$) whose neighbourhood test $T$ is $(\varepsilon_0,\eta_0,c,C)$-sound, where $\varepsilon_0,\eta_0\in(0,1)$, $0<c\le1$ and $C\ge1$. Put $\delta=c\varepsilon_0^C$ and fix $\eta_0<\gamma\le1$. For every finite alphabet $\Sigma$ and every local ensemble $F=(f_v:X_v[2]\to\Sigma)_{v\in X[1]\cup X[3]}$ there is a list $L$ of global functions $X[2]\to\Sigma$ with
--   $$|L|\le\frac{\mathrm{Agr}(F)}{\delta},\qquad \mathrm{supp}^{\eta_0}(g)>\delta\ \ (g\in L),\qquad \mathrm{Agr}(F)-\mathrm{supp}_\gamma(L)\le\varepsilon_0+\frac{8|L|\lambda^2}{(\gamma-\eta_0)^2},$$
--   where $\mathrm{supp}_\gamma(L)$ is the probability that the test passes and both endpoint functions are $\gamma$-close to the same member of $L$, distances measured on their neighbourhoods.
--
--   It combines the two single-colour tests in the proof of Theorem 6.1 and yields the lists of Lemma 3.4.
--
--   Differences from the source:
--   - reading: a 3-partite λ-product complex → IsProduct X λ with 0 ≤ λ ≤ 1; reason: [0, 1] is the range of Definition 2.11
--   - encoding: colours 1, 2, 3 of a 3-partite complex → Fin 3 with 0-based indices 0, 1, 2; reason: Lean convention; same instances
--   - encoding: the list L and |L| → a List of functions V 1 → Sig and its length; reason: a list may repeat entries, as the erasure process allows
--   - encoding: a nonempty finite alphabet Σ → a type Sig : Type with Fintype (and Nonempty where the source asks for it); reason: every finite alphabet is in bijection with a type in Type 0
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 43, Lemma 6.12 (proved in Appendix B, pp. 62-63)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Agreement

namespace HDXNbhdPCP.Main

/-- Lemma 6.12: list decoding a sound neighbourhood test. The colours `1, 2, 3` of the paper are
`0, 1, 2`; `δ = c ε₀^C`. -/
theorem lemma_6_12 {V : Fin 3 → Type} (X : ColoredComplex (Fin 3) V) (hX : FinDist.IsProb X)
    (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (hprod : X.IsProduct lam)
    (ε₀ η₀ c C : ℝ) (hε₀ : 0 < ε₀ ∧ ε₀ < 1) (hη₀ : 0 < η₀ ∧ η₀ < 1) (hc : 0 < c ∧ c ≤ 1)
    (hC : 1 ≤ C) (hsound : (X.nbhdTestOn 0 1 2).IsSound ε₀ η₀ c C)
    (γ : ℝ) (hγ : η₀ < γ ∧ γ ≤ 1) {Sig : Type} [Fintype Sig] (F : V 0 ⊕ V 2 → V 1 → Sig) :
    ∃ L : List (V 1 → Sig),
      (L.length : ℝ) ≤ (X.nbhdTestOn 0 1 2).Agr F / (c * ε₀ ^ C) ∧
      (∀ g ∈ L, (X.nbhdTestOn 0 1 2).edgeSupp F g η₀ > c * ε₀ ^ C) ∧
      (X.nbhdTestOn 0 1 2).Agr F - (X.nbhdTestOn 0 1 2).listSupp F L γ ≤
        ε₀ + 8 * L.length * lam ^ 2 / (γ - η₀) ^ 2 := by sorry

end HDXNbhdPCP.Main
