-- Prove2me | Theorems.Thm_FourToOneGames_grassmann_equality_decoding
-- name    : FourToOneGames.grassmann_equality_decoding
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T23:29:20.679296+00:00
-- url     : https://prove2.me/theorems/b242ed97-f0dc-4c78-8afb-8be26dee00bd
-- title:
--   Theorem 3.3 — decoding for the Grassmann equality test
-- statement:
--   The companion of Theorem 3.2 for tables with values in an arbitrary finite set.
--
--   There is an absolute constant $C > 0$ such that for every finite set $\Sigma$ and all $n, \ell, q$ with $n - q \ge \ell \ge q+1$ the following holds. Let $F$ assign to each $\ell$-dimensional subspace $L \subseteq \mathbb{F}_2^n$ an element of $\Sigma$ or the nullity element, and suppose
--
--   $$\Pr_{(L_1,L_2)}\big[F[L_1] = F[L_2] \ne \mathrm{nil}\big] \ge 2^{-q+4}$$
--
--   for a uniformly random edge $(L_1,L_2)$ of the Grassmann graph. Then for at least a $2^{-q-\ell^2}$ fraction of the $q$-dimensional subspaces $Q$ there are an element $\sigma \in \Sigma$ and a subspace $W$ of dimension $n-q$ containing $Q$ with
--
--   $$\Pr_{L}\big[F[L] = \sigma \ \big|\ Q \subseteq L \subseteq W\big] \ge 2^{-Cq^2}.$$
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, p. 16, Theorem 3.3 (proof in Appendix D, pp. 89-93)

import Definitions.Def_FourToOneGames_Grassmann

namespace FourToOneGames

theorem grassmann_equality_decoding :
    ∃ C : ℕ, 0 < C ∧ ∀ (σType : Type) [Fintype σType], ∀ n ℓ q : ℕ, q + ℓ ≤ n → q + 1 ≤ ℓ →
      ∀ F : SetTable n σType, (2 : ℝ) ^ (4 - (q : ℤ)) ≤ grEqualityTestProb ℓ F →
        (2 : ℝ) ^ (-(q : ℤ) - (ℓ : ℤ) ^ 2) ≤
          grFraction n q (fun Q => ∃ (σ : σType) (W : Submodule (ZMod 2) (Fspace n)),
            Q ≤ W ∧ codim W = q ∧
              (2 : ℝ) ^ (-((C : ℤ) * (q : ℤ) ^ 2)) ≤ zoomAgreementConst ℓ F Q W σ) := by
  sorry

end FourToOneGames
