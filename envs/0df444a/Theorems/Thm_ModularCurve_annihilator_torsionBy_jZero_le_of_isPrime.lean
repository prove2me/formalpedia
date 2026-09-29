-- Prove2me | Theorems.Thm_ModularCurve_annihilator_torsionBy_jZero_le_of_isPrime
-- name    : ModularCurve.annihilator_torsionBy_jZero_le_of_isPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/5264a408-9ecd-5521-8bbb-aeedbf98a9c3
-- title:
--   Primes of residue characteristic p lie in the support of J₀(N)[p]
-- statement:
--   Fix $N\ge 1$ and a prime $p$. Let $\mathrm{JZero}\,N$ denote $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$, that is, degree-zero divisors modulo principal divisors, and let `HeckeAlg` be the polynomial ring $\mathbb Z[X_\ell : \ell\ \text{prime}]$ on indeterminates indexed by the primes. Assume `HeckeInputsAll N`, i.e. for every prime $\ell$ the package `HeckeInputsAlong` over $\overline{\mathbb Q}$ at level $N$ and $\ell$ (integrality of the two divisorial correspondences, principality of divisors at level $N\ell$, finiteness, the fundamental identity and the norm formula) holds; and assume `HeckeOperatorsCommuteBar N`, i.e. the endomorphisms `heckeOperatorBar N ℓ` of $\mathrm{JZero}\,N$ commute pairwise, so that the `HeckeAlg`-module structure `heckeModuleBar N` on $\mathrm{JZero}\,N$ is the one sending each indeterminate to the corresponding Hecke operator. Let $\mathfrak p$ be a prime ideal of `HeckeAlg` containing the annihilator of $\mathrm{JZero}\,N$ and containing the image of $p$. The conclusion is that the annihilator of the $p$-torsion submodule $\{x : p\cdot x = 0\}$ of $\mathrm{JZero}\,N$ is contained in $\mathfrak p$.
--
--   Equivalently: every prime of the divisorial Hecke algebra of $J_0(N)$ of residue characteristic $p$ lies in the support of $J_0(N)[p]$, the finite-level shadow of the faithfulness of the Hecke action on the $p$-adic Tate module. It is used in the construction of the eigenform attached to a maximal ideal in the support of $J_0(N)$, via [`ModularCurve.eigenformSupportAt_jZero`](thm.html#ModularCurve.eigenformSupportAt_jZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_annihilator_torsionBy_jZero_le_of_isPrime.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.annihilator_torsionBy_jZero_le_of_isPrime (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime)
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (𝔭 : Ideal ModularCurve.HeckeAlg) (h𝔭 : 𝔭.IsPrime)
    (hann : letI := ModularCurve.heckeModuleBar N;
      Module.annihilator ModularCurve.HeckeAlg (ModularCurve.JZero N) ≤ 𝔭)
    (hp𝔭 : (p : ModularCurve.HeckeAlg) ∈ 𝔭) :
    letI := ModularCurve.heckeModuleBar N
    (Submodule.torsionBy ModularCurve.HeckeAlg (ModularCurve.JZero N) (p : ModularCurve.HeckeAlg)).annihilator ≤ 𝔭 := by sorry
