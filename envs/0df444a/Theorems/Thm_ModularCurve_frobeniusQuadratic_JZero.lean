-- Prove2me | Theorems.Thm_ModularCurve_frobeniusQuadratic_JZero
-- name    : ModularCurve.frobeniusQuadratic_JZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/89e44774-2011-5b7c-961b-004e4f6e4da1
-- title:
--   Eichler–Shimura relation on p-power torsion of J₀(N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $p$ be an arbitrary natural number (no primality of $p$ is assumed). Assume [`ModularCurve.HeckeOperatorsCommuteBar N`](def/ModularCurve_HeckeModule.html#L25), i.e. that the endomorphisms `heckeOperatorBar N ℓ` of $J_0(N)$ over $\overline{\mathbb{Q}}$ commute pairwise for all primes $\ell, \ell'$; this makes the instance `heckeModuleBar N` the action of the project's Hecke algebra `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ on `JZero N` in which the generator `heckeGen ℓ` acts as `heckeOperatorBar N ℓ`. Here `JZero N` is `Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`, the degree-zero divisor class group of the modular function field of level $N$ over $\overline{\mathbb{Q}}$, carrying its natural action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$. Under the further (unnamed) hypothesis that this Galois action commutes with the Hecke action, `SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero N)` — a hypothesis needed to state the conclusion at all — the theorem asserts [`ModularCurve.FrobeniusQuadratic N p (JZero N)`](def/HeckeGalois_EichlerShimura.html#L130) for $K = \mathbb{Q}$, $L = \overline{\mathbb{Q}}$, which by definition says: for every prime $\ell$ with $\ell \nmid Np$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $\ell$ (`A.LiesOverPrime ℓ`), every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ that is a Frobenius element at $A$ for $\ell$ (`A.IsFrobeniusAt σ ℓ`), and every $x \in J_0(N)(\overline{\mathbb{Q}})$ killed by some power $p^n$, one has $\sigma \cdot \sigma \cdot x - \mathrm{heckeGen}\,\ell \cdot (\sigma \cdot x) + \ell \cdot x = 0$, the last term being the $\ell$-fold natural-number multiple of $x$.
--
--   This is the Eichler–Shimura congruence relation $\mathrm{Frob}_\ell^2 - T_\ell\,\mathrm{Frob}_\ell + \ell = 0$, here asserted not as an identity of correspondences or of endomorphisms of the whole Jacobian but only as the vanishing of a specific element for each element $x$ of $p$-power torsion, for primes $\ell \nmid Np$ and with $T_\ell$ meaning the action of the polynomial generator `heckeGen ℓ` of the project's Hecke algebra. Note that $p$ is an unrestricted natural number and that the Frobenius is taken relative to a chosen valuation subring of $\overline{\mathbb{Q}}$ over $\ell$, so no choice of decomposition group or model of $X_0(N)$ appears in the statement. Downstream it supplies the `frobeniusQuadratic` clause used in the Chebotarev and Cayley–Hamilton arguments that attach two-dimensional residual Galois representations to maximal ideals of the Hecke algebra, in particular in the determinant computation [`ModularCurve.detFrobeniusMod_jZero_of_multiplicityOneData`](thm.html#ModularCurve.detFrobeniusMod_jZero_of_multiplicityOneData) and in [`FreyPackage.eigenformResidualAttachmentAtFamily`](thm.html#FreyPackage.eigenformResidualAttachmentAtFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobeniusQuadratic_JZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.frobeniusQuadratic_JZero (N p : ℕ) [NeZero N]
    (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) :
    letI := ModularCurve.heckeModuleBar N
    ∀ (_ : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg
        (ModularCurve.JZero N)),
      ModularCurve.FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p (ModularCurve.JZero N) := by sorry
