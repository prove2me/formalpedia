-- Prove2me | Theorems.Thm_ModularCurve_LevelP_exists_levelPData_map_eq_relabel_univData
-- name    : ModularCurve.LevelP.exists_levelPData_map_eq_relabel_univData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/05500e9d-3fba-558c-bc6c-db4931caca6e
-- title:
--   Universal relabelling of the level-ℓ basis exists
-- statement:
--   Let $\ell$ be a natural number that is prime and satisfies $\ell \ge 3$, and let $g$ be a $2\times 2$ matrix with integer entries whose reduction modulo $\ell$ has determinant a unit in $\mathbb{Z}/\ell$. Write $\mathcal{T} =$ [`ModularCurve.LevelP.UnivBasisRing`](def/ModularCurve_KatzLevelPUniversal.html#L274) $\ell$, the localisation of the two-point ring of the universal Weierstrass curve away from the element `indepDenom`, carrying the base-changed curve $E =$ `univCurveT` $\ell$ over $\mathcal{T}$ and the quadruple `univData` $\ell$ consisting of the images in $\mathcal{T}$ of the universal coordinates $x_P, y_P, x_Q, y_Q$. The assertion is that there is a single quadruple $R = (x_{P'}, y_{P'}, x_{Q'}, y_{Q'}) \in \mathcal{T}^4$ (an element of `LevelPData` $\mathcal{T}$) with the following property: for every field $F$ and every ring homomorphism $\varphi : \mathcal{T} \to F$, the componentwise image of $R$ under $\varphi$ coincides with the relabelling of the specialised datum. Here the relabelling is computed as follows: over $F$ one forms the points $P = (\varphi x_P, \varphi y_P)$ and $Q = (\varphi x_Q, \varphi y_Q)$ of the affine curve $E_\varphi$ if these coordinate pairs are nonsingular solutions, and the point at infinity otherwise; one then takes $g_{00}\cdot P + g_{10}\cdot Q$ and $g_{01}\cdot P + g_{11}\cdot Q$ in the group $E_\varphi(F)$, and records the affine coordinates of each, with the convention that the point at infinity is recorded as $(0,0)$.
--
--   This is the existence half of the statement that $\mathrm{GL}_2(\mathbb{Z}/\ell)$ acts by relabelling on the universal level-$\ell$ structure: the new basis $(aP+cQ, bP+dQ)$ is cut out by elements of the universal base ring $\mathcal{T}$ itself, uniformly in all field-valued points. It is used by [`ModularCurve.LevelRelabelling.exists_natural_relabel_levelPData`](thm.html#ModularCurve.LevelRelabelling.exists_natural_relabel_levelPData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_exists_levelPData_map_eq_relabel_univData.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelP.exists_levelPData_map_eq_relabel_univData
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) :
    ∃ R : LevelPData (ModularCurve.LevelP.UnivBasisRing ℓ),
      ∀ (F : Type u) [Field F] (φ : ModularCurve.LevelP.UnivBasisRing ℓ →+* F),
        R.map φ = LevelRelabelling.LevelPData.relabel ((ModularCurve.LevelP.univCurveT ℓ).map φ) g
          ((ModularCurve.LevelP.univData ℓ).map φ) := by sorry
