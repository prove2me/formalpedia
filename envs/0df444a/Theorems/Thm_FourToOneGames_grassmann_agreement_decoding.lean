-- Prove2me | Theorems.Thm_FourToOneGames_grassmann_agreement_decoding
-- name    : FourToOneGames.grassmann_agreement_decoding
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T23:07:51.489955+00:00
-- url     : https://prove2.me/theorems/74c5fd94-7811-409c-8f28-072328209745
-- title:
--   Theorem 3.2 — Grassmann agreement test decoding
-- statement:
--   The soundness of the Grassmann agreement test, in the formulation the source paper derives from Khot–Minzer–Safra.
--
--   There is an absolute constant $C > 0$ such that the following holds for all $n, \ell, q$ with $n - q \ge \ell \ge q+1$. Let $F$ be a table assigning to each $\ell$-dimensional subspace $L \subseteq \mathbb{F}_2^n$ either a linear functional on $L$ or the nullity element, and suppose the Grassmann test passes with probability at least $2^{-q+5}$, i.e.
--
--   $$\Pr_{(L_1,L_2)}\big[F[L_1]|_{L_1 \cap L_2} = F[L_2]|_{L_1 \cap L_2}\big] \ge 2^{-q+5},$$
--
--   where $(L_1,L_2)$ is a uniformly random edge of the Grassmann graph and the event fails if either entry is nil. Then for at least a $2^{-q-\ell^2}$ fraction of the $q$-dimensional subspaces $Q$ there are a subspace $W$ of dimension $n-q$ containing $Q$ and a linear map $f : W \to \mathbb{F}_2$ with
--
--   $$\Pr_{L}\big[F[L] = f|_L \ \big|\ Q \subseteq L \subseteq W\big] \ge 2^{-Cq^2}.$$
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, p. 16, Theorem 3.2 (proof in Appendix D, pp. 89-93)

import Definitions.Def_FourToOneGames_Grassmann

namespace FourToOneGames

theorem grassmann_agreement_decoding :
    ∃ C : ℕ, 0 < C ∧ ∀ n ℓ q : ℕ, q + ℓ ≤ n → q + 1 ≤ ℓ →
      ∀ F : LinTable n, (2 : ℝ) ^ (5 - (q : ℤ)) ≤ grTestProb ℓ F →
        (2 : ℝ) ^ (-(q : ℤ) - (ℓ : ℤ) ^ 2) ≤
          grFraction n q (fun Q => ∃ W : Submodule (ZMod 2) (Fspace n), Q ≤ W ∧ codim W = q ∧
            ∃ f : W →ₗ[ZMod 2] ZMod 2,
              (2 : ℝ) ^ (-((C : ℤ) * (q : ℤ) ^ 2)) ≤ zoomAgreementLin ℓ F Q W f) := by
  sorry

end FourToOneGames
