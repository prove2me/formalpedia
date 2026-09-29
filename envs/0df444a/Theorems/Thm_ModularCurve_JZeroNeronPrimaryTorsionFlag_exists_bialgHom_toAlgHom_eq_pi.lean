-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_bialgHom_toAlgHom_eq_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/823b0ba2-3446-5f4d-8621-3c6ffa1fb7be
-- title:
--   Flag projections are ℤ-bialgebra maps
-- statement:
--   Let $p$ and $q$ be primes, let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that the image of $p$ lies in `A.nonunits`, let $C$ be a datum of type `JZeroNeronPrimaryTorsionCore p q A hA` — in particular a family of fppf sheaves `C.𝒥 m` of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb Z$ together with commutative $\mathbb Z$-Hopf algebras `C.H m` of finite type and flat over $\mathbb Z$, an additive identification of the sections of `C.𝒥 m` over each object $U$ with the convolution group of $\mathbb Z$-algebra maps `C.H m → Γ(U.left, ⊤)`, and the arithmetic data relating its generic and $p$-fibre points to `eisensteinPrimaryTorsionBar p q m` — and let $m$ be a natural number. Let `flag` be a flag structure of type `JZeroNeronPrimaryTorsionFlag p q A hA C m`, whose fields (a length `flag.n`, commutative flat $\mathbb Z$-Hopf algebras `flag.G i` of finite type with surjective $\mathbb Z$-algebra maps `flag.π i : C.H m →ₐ[ℤ] flag.G i` and compatible transition maps, subobjects `flag.F i ⟶ C.𝒥 m` whose sections are identified with convolution groups of $\mathbb Z$-algebra maps out of `flag.G i` compatibly with `flag.π i`, and a monotone Galois-stable filtration `flag.genericStep` of `eisensteinPrimaryTorsionBar p q m`) are summarised here. Then for every index $i$ in `Fin (flag.n + 1)` there is a $\mathbb Z$-bialgebra homomorphism `C.H m →ₐc[ℤ] flag.G i` whose underlying $\mathbb Z$-algebra homomorphism is exactly `flag.π i`.
--
--   The flag data type its projections `flag.π i` only as maps of $\mathbb Z$-algebras; this result upgrades each of them to a map of bialgebras, so that the corresponding closed immersion of affine schemes over $\operatorname{Spec}\mathbb Z$ is a homomorphism of group schemes, as required in Mazur's analysis of a filtration of the $\mathfrak P$-primary torsion of the Jacobian by finite flat subgroup schemes. It is used in the identification of convolution powers of algebra maps in the step with multiplicative type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_bialgHom_toAlgHom_eq_pi
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin (flag.n + 1)) :
    ∃ πc : C.H m →ₐc[ℤ] flag.G i, (πc : C.H m →ₐ[ℤ] flag.G i) = flag.π i := by sorry
