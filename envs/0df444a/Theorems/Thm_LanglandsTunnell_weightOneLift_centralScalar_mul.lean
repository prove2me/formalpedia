-- Prove2me | Theorems.Thm_LanglandsTunnell_weightOneLift_centralScalar_mul
-- name    : LanglandsTunnell.weightOneLift_centralScalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c97022ef-45a1-55f8-83f6-a374c0472be4
-- title:
--   Central character of the adelic weight-one lift
-- statement:
--   Fix a nonzero natural number $n$, a function $f : \mathfrak{H} \to \mathbb{C}$ on the upper half-plane, and a Dirichlet character $\chi$ modulo $n$ with values in $\mathbb{C}$. Assume $f \mid[1] \varepsilon = f$ for every $\varepsilon \in \Gamma_1(n) \subseteq \mathrm{SL}_2(\mathbb{Z})$, and $f \mid[1] \gamma = \chi(d)\, f$ for every $\gamma \in \Gamma_0(n)$ with lower-right entry $d = \gamma_{11}$, the weight-one slash action being taken through the inclusion $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{GL}_2(\mathbb{R})$. Write $F =$ `weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f` for the adelic lift at level $(n)$: on an element of $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ admitting a decomposition $\gamma \cdot h \cdot u$ with $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, $h$ of trivial finite part and with real archimedean component of positive determinant, and $u$ in the level-$(n)$ subgroup of the compact production data over $\mathbb{Q}$, its value is $(f \mid[1] h_\infty)(i)\cdot \det(h_\infty)$ for a chosen such decomposition, and $0$ otherwise. The conclusion: for every $z$ in the central subgroup of `productionPinsCompact ℚ`, which is all of $\mathbb{A}_\mathbb{Q}^\times$, and every $g \in \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, one has $F(\mathrm{diag}(z,z)\, g) = c(z)\, F(g)$, where $c(z) \in \mathbb{C}$ is the value at $z$ of the product of the idele character attached to $\chi$ (the inverse of $\chi$ evaluated on the unit residue of an idele modulo $n$) with the distributive Haar character of $\mathbb{A}_\mathbb{Q}$, the latter pushed from $\mathbb{R}_{\ge 0}^\times$ into $\mathbb{C}^\times$.
--
--   This is the central transformation law of the adelic lift of a classical weight-one form of level $n$ and nebentypus $\chi$: the scalar ideles act through the idele character of $\chi$ times the adelic modulus, the modulus appearing because the lift carries the determinant factor of the archimedean component. It is used in the construction of the dihedral weight-one automorphic realisation, both for the comparison of the lift with a smooth cusp form on the production pins and for its non-vanishing, and in the companion law for scalars times Hecke generators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_weightOneLift_centralScalar_mul.lean

import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_DirichletCharacter_DirichletIdeleChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.weightOneLift_centralScalar_mul
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f) :
    ∀ (z : (productionPinsCompact ℚ).Z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g)
        = ((((DirichletCharacter.dirichletIdeleChar χ *
            (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
              (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          (productionPinsCompact ℚ).Z.subtype) z : ℂˣ) : ℂ) * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by sorry
