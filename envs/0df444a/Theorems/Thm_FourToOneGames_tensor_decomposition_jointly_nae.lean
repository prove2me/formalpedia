-- Prove2me | Theorems.Thm_FourToOneGames_tensor_decomposition_jointly_nae
-- name    : FourToOneGames.tensor_decomposition_jointly_nae
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T23:38:54.721906+00:00
-- url     : https://prove2.me/theorems/c3c19c79-898a-4eb7-b7a2-f312c198513c
-- title:
--   Proposition 4.13 — a tensor decomposition of an NAE-satisfying form is jointly NAE-satisfying
-- statement:
--   Let $E$ be a tripled set and $r$ a positive integer. If $f : \mathbb{F}_2^{E} \otimes \mathbb{F}_2^{E} \to \mathbb{F}_2$ is an NAE-satisfying symmetric bilinear map, then any tensor decomposition $(f^{(1)}, \dots, f^{(r)})$ of $f$ is jointly NAE-satisfying.
--
--   Here $f$ is NAE-satisfying when its matrix $X$ obeys $X_{v_1v_1}+X_{v_2v_2}+X_{v_3v_3}+X_{v_1v_2}+X_{v_2v_3}+X_{v_3v_1} = 1$ for every triple $\{v_1,v_2,v_3\}$ of $E$, a tensor decomposition is a family of linear functionals $f^{(i)}$ lying in the image of $x \mapsto f(x \otimes \cdot)$ with $f(x \otimes y) = \sum_i f^{(i)}(x) f^{(i)}(y)$, and joint NAE-satisfiability means $\sum_i \mathrm{NAE}_3(a^{(i)}_{v_1}, a^{(i)}_{v_2}, a^{(i)}_{v_3}) = 1$ for every triple, $a^{(i)}$ being the coefficient vector of $f^{(i)}$.
--
--   The formal statement allows an arbitrary $r \ge 0$, which includes the case $r$ positive considered in the source.
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, pp. 21-22, Proposition 4.13

import Definitions.Def_FourToOneGames_NAE

namespace FourToOneGames

theorem tensor_decomposition_jointly_nae {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (hsymm : IsSymmetricForm f) (hnae : NAESatisfyingForm f)
    (φ : Fin r → TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (hdec : IsTensorDecomposition f φ) :
    JointlyNAESatisfying φ := by
  sorry

end FourToOneGames
