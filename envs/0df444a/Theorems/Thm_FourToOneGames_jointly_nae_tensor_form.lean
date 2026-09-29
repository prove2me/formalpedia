-- Prove2me | Theorems.Thm_FourToOneGames_jointly_nae_tensor_form
-- name    : FourToOneGames.jointly_nae_tensor_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T23:41:11.533086+00:00
-- url     : https://prove2.me/theorems/6054ff20-9c05-4561-b818-f408ab75e730
-- title:
--   Proposition 4.14 — converse: a jointly NAE-satisfying decomposition yields an NAE-satisfying form
-- statement:
--   Let $E$ be a tripled set and $r$ a positive integer. Suppose $f : \mathbb{F}_2^{E} \otimes \mathbb{F}_2^{E} \to \mathbb{F}_2$ is a symmetric bilinear map and $f^{(1)}, \dots, f^{(r)} : \mathbb{F}_2^{E} \to \mathbb{F}_2$ are jointly NAE-satisfying linear functionals. If $f(x \otimes y) = \sum_i f^{(i)}(x) f^{(i)}(y)$ holds for all $x, y$, then $f$ is NAE-satisfying.
--
--   Only the displayed identity is assumed, not the additional requirement (part of the definition of a tensor decomposition) that each $f^{(i)}$ lie in the image of $x \mapsto f(x \otimes \cdot)$; and $r$ is allowed to be any natural number.
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, p. 22, Proposition 4.14

import Definitions.Def_FourToOneGames_NAE

namespace FourToOneGames

theorem jointly_nae_tensor_form {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (hsymm : IsSymmetricForm f)
    (φ : Fin r → TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (hφ : JointlyNAESatisfying φ)
    (hexp : ∀ x y : TripledSpace ι, f x y = ∑ j : Fin r, φ j x * φ j y) :
    NAESatisfyingForm f := by
  sorry

end FourToOneGames
