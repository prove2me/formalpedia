-- Prove2me | Theorems.Thm_FourToOneGames_exists_rank_one_nae_form
-- name    : FourToOneGames.exists_rank_one_nae_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T23:41:37.798906+00:00
-- url     : https://prove2.me/theorems/5a15f1c9-26dc-465f-9d5d-e5dff3efff81
-- title:
--   Corollary 4.15 — existence of a rank-one NAE-satisfying bilinear form
-- statement:
--   Let $E$ be a nonempty tripled set. Then there exists an NAE-satisfying symmetric bilinear map $f : \mathbb{F}_2^{E} \otimes \mathbb{F}_2^{E} \to \mathbb{F}_2$ of rank $1$, i.e. one of the form $f(x \otimes y) = \phi(x)\phi(y)$ for a non-zero linear functional $\phi$. This provides the honest prover strategy used in the completeness analysis of the outer PCP.
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, p. 22, Corollary 4.15

import Definitions.Def_FourToOneGames_NAE

namespace FourToOneGames

theorem exists_rank_one_nae_form {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∃ f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2,
      IsSymmetricForm f ∧ NAESatisfyingForm f ∧
        ∃ φ : TripledSpace ι →ₗ[ZMod 2] ZMod 2, φ ≠ 0 ∧
          ∀ x y : TripledSpace ι, f x y = φ x * φ y := by
  sorry

end FourToOneGames
