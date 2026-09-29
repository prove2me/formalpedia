-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_of_range_eq_hopfKer_of_kind_eq_const
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.ringEquiv_apply_algHom_eq_of_range_eq_hopfKer_of_kind_eq_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/90db51af-81f8-5f30-8769-53936773c854
-- title:
--   Constant-kind flag layers have Galois-invariant ℚ̄-points
-- statement:
--   Let $p$ and $q$ be primes, let $A$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ lying in the nonunits of $A$, let $C$ be a datum of type `JZeroNeronPrimaryTorsionCore p q A hA` (the family of fppf sheaves $\mathcal J_m$ on the small fppf site of $\operatorname{Spec}\mathbf Z$ together with the finite-type flat Hopf $\mathbf Z$-algebras $H_m$ representing them and their identifications of generic and $A$-integral points with the $\mathfrak P$-primary $q^m$-torsion of $J_0(p)$), let $m\in\mathbf N$ and let `flag` be a flag of type `JZeroNeronPrimaryTorsionFlag p q A hA C m`, consisting of Hopf $\mathbf Z$-algebras $G_0,\dots,G_{\mathrm{flag}.n}$ with surjections from $H_m$, surjective quotient maps $\mathrm{quot}\,i : G_{i+1}\to G_i$ compatible with them, matching subsheaves $F_i\hookrightarrow \mathcal J_m$, Galois-stable generic steps, and a label $\mathrm{kind}$ on each layer. Fix a layer index $i$ with $\mathrm{flag.kind}\,i = \mathtt{const}$, and a bialgebra map $qc : G_{i+1}\to G_i$ whose underlying $\mathbf Z$-algebra map is $\mathrm{quot}\,i$. Let $K$ be a commutative Hopf $\mathbf Z$-algebra together with an injective bialgebra map $j : K \to G_{i+1}$ whose image is the Hopf kernel $\mathrm{hopfKer}\,qc$, the equalizer inside $G_{i+1}$ of the coaction $(\mathrm{id}\otimes qc)\circ\Delta$ and $a\mapsto a\otimes 1$, and assume $G_{i+1}$ is faithfully flat as a module over that subalgebra. Then for every ring automorphism $\sigma$ of $\overline{\mathbf Q}$, every $\mathbf Z$-algebra map $\psi : K \to \overline{\mathbf Q}$ and every $k\in K$ one has $\sigma(\psi(k)) = \psi(k)$.
--
--   The conclusion says that every $\overline{\mathbf Q}$-point of the layer cut out by the Hopf kernel of a constant-kind step of the flag takes values fixed by all ring automorphisms of $\overline{\mathbf Q}$, i.e. in $\mathbf Q$; this is the rationality statement that makes such a layer behave like a constant group scheme. It is used in the finiteness and order computations for the fppf cohomology of the cokernel of a constant-kind step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_of_range_eq_hopfKer_of_kind_eq_const.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.ringEquiv_apply_algHom_eq_of_range_eq_hopfKer_of_kind_eq_const
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.const)
    (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hqc : (qc : flag.G i.succ →ₐ[ℤ] flag.G i.castSucc) = flag.quot i)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K)
    (j : K →ₐc[ℤ] flag.G i.succ) (hinj : Function.Injective j)
    (hrange : (j : K →ₐ[ℤ] flag.G i.succ).range = HopfAlgebra.hopfKer qc)
    (hflat : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) (flag.G i.succ)) :
    ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k := by sorry
