-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
-- name    : ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/1408c767-5005-50cf-ab82-eb6e749e38c8
-- title:
--   Hecke-equivariant comparison TₚJ₀(N)≅mathbb Zₚ⊗ H₁
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime. Three hypotheses are imposed: [`ModularCurve.HeckeInputsAll N`](def/ModularCurve_HeckeInputsAll.html#L8), asserting that for every prime $\ell$ the predicate `HeckeInputsAlong` holds over $\overline{\mathbb Q}$ at level $N$ and prime $\ell$ (the data needed to construct the $\ell$-th Hecke correspondence); [`ModularCurve.HeckeOperatorsCommuteBar N`](def/ModularCurve_HeckeModule.html#L25), asserting that the endomorphisms `heckeOperatorBar N ℓ` commute pairwise as $\ell$ runs over the primes; and [`ModularCurve.PeriodLatticeHeckeStable N`](def/ModularCurve_PeriodLattice.html#L223), asserting that for each prime $\ell$ the operator `dualHeckeRep N (heckeGen ℓ)` maps the lattice `periodLattice N` — the $\mathbb Z$-span of the range of `period N` inside the complex-linear dual of $S_2(\Gamma_0(N))=$ `CuspForm (CongruenceSubgroup.Gamma0 N) 2` — into itself. Equip $J_0(N)=$ [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the group of degree-zero divisor classes modulo principal divisors of `modularFunctionFieldBar N` over $\overline{\mathbb Q}$, with the module structure `heckeModuleBar N` over `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$, which by the commutativity hypothesis is the action sending $X_\ell$ to `heckeOperatorBar N ℓ`. The conclusion is the existence of a $\mathbb Z_p$-linear isomorphism $e$ from [`TateModule p (JZero N)`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_n)$ in $J_0(N)$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$, onto $\mathbb Z_p\otimes_{\mathbb Z}$ `periodLattice N`, such that for every $t\in$ `HeckeAlg` and every $x$ one has $e(\,t\cdot x\,)=\bigl(1\otimes$ `periodLatticeHeckeEnd N t`$\bigr)(e(x))$, the action on the Tate module being levelwise and `periodLatticeHeckeEnd N` being, under the stability hypothesis, the restriction of `dualHeckeRep N` to the lattice.
--
--   This is the transcendental comparison between the $p$-adic Tate module of $J_0(N)$ over $\overline{\mathbb Q}$ and the first integral homology of $X_0(N)$, in the form $T_pJ_0(N)\cong \mathbb Z_p\otimes_{\mathbb Z}H_1(X_0(N),\mathbb Z)$ with the Hecke actions matched. It is the source of the rank-two statements about Hecke eigenspaces in $T_pJ_0(N)$ and of the Frobenius-trace computations used to attach Galois representations to newforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (hst : ModularCurve.PeriodLatticeHeckeStable N) :
    letI := ModularCurve.heckeModuleBar N
    ∃ e : TateModule p (ModularCurve.JZero N) ≃ₗ[ℤ_[p]]
        TensorProduct ℤ ℤ_[p] (ModularCurve.periodLattice N),
      ∀ (t : ModularCurve.HeckeAlg) (x : TateModule p (ModularCurve.JZero N)),
        e (ModularCurve.tateHeckeRep p (ModularCurve.JZero N) t x) =
          (ModularCurve.periodLatticeHeckeEnd N t).baseChange ℤ_[p] (e x) := by sorry
