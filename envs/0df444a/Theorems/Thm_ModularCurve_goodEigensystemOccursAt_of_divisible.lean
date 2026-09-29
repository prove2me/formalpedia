-- Prove2me | Theorems.Thm_ModularCurve_goodEigensystemOccursAt_of_divisible
-- name    : ModularCurve.goodEigensystemOccursAt_of_divisible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/6ccd1510-e7a9-560d-ae38-8fabd24fb63b
-- title:
--   Divisible subgroup killed by the good eigenideal lowers the level
-- statement:
--   Let $N_0$ and $p$ be nonzero natural numbers. Assume [`ModularCurve.HeckeInputsAll N_0`](def/ModularCurve_HeckeInputsAll.html#L8), i.e. for every prime $\ell$ the package `HeckeInputsAlong` of integrality, finiteness, fundamental-identity and norm-formula conditions holds over $\overline{\mathbb{Q}}$ for level $N_0$ and $\ell$, and assume `HeckeOperatorsCommuteBar N_0`, i.e. the endomorphisms $\mathrm{heckeOperatorBar}\,N_0\,\ell$ of $J_0(N_0) = \mathrm{Pic}^0$ of the modular function field of level $N_0$ base changed to $\overline{\mathbb{Q}}$ (degree-zero divisor classes modulo principal divisors) commute pairwise. Let $f$ be a weight-$2$ cusp form on $\Gamma_0(N_0p)$ which is a normalized eigenform in the sense of `IsNormalizedEigenform`: its $q$-coefficients satisfy $a_1 = 1$, multiplicativity at coprime indices, and the recursions $a_{q^{r+2}} = a_q a_{q^{r+1}} - q\,a_{q^r}$ for primes $q \nmid N_0p$ and $a_{q^{r+2}} = a_q a_{q^{r+1}}$ for $q \mid N_0p$. Let $D$ be a nonzero additive subgroup of $J_0(N_0)$ which is divisible, in the sense that for every $y \in D$ and every $n > 0$ there is $z \in D$ with $n\,z = y$. Suppose finally that every element $t$ of `eigenIdeal` of $\ell \mapsto a_\ell(f)$ — the kernel of the evaluation $\mathbb{Z}[x_\ell : \ell \text{ prime}] \to \mathbb{C}$, $x_\ell \mapsto a_\ell(f)$ — which is supported on the variables indexed by primes not dividing $N_0p$ annihilates $D$, the module structure being `heckeModuleBar N_0` (which, the commutation hypothesis holding, lets $x_\ell$ act by $\mathrm{heckeOperatorBar}\,N_0\,\ell$). Then the good eigensystem of $f$ occurs at level $N_0$: there is a weight-$2$ normalized eigenform $g$ on $\Gamma_0(N_0)$ with $a_\ell(g) = a_\ell(f)$ for every prime $\ell \nmid N_0p$.
--
--   This is the level-lowering step in its geometric form: a nonzero divisible subgroup of $J_0(N_0)$ on which the good-prime eigenvalue ideal of a form of level $N_0p$ acts as zero produces a form of level $N_0$ with the same $\ell$-th coefficients for all $\ell \nmid N_0p$. It is used in the construction of the Galois representations and eigenplanes attached to newforms inside the Tate module of $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_goodEigensystemOccursAt_of_divisible.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.goodEigensystemOccursAt_of_divisible
    (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hin : ModularCurve.HeckeInputsAll N₀) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N₀)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (N₀ * p)) 2) (hf : f.IsNormalizedEigenform)
    (D : AddSubgroup (ModularCurve.JZero N₀)) (hD : D ≠ ⊥)
    (hdiv : ∀ y ∈ D, ∀ n : ℕ, 0 < n → ∃ z ∈ D, n • z = y)
    (hkill : ∀ t ∈ ModularCurve.eigenIdeal (fun ℓ : Nat.Primes => ModularFormClass.qCoeff f ℓ),
      t ∈ MvPolynomial.supported ℤ {ℓ : Nat.Primes | ¬ (ℓ : ℕ) ∣ N₀ * p} →
      ∀ y ∈ D, (letI := ModularCurve.heckeModuleBar N₀; t • y) = 0) :
    f.GoodEigensystemOccursAt N₀ := by sorry
