-- Prove2me | Theorems.Thm_ModularCurve_exists_linearEquiv_rationalTateModule_tensor_periodLattice
-- name    : ModularCurve.exists_linearEquiv_rationalTateModule_tensor_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/29d9f2a5-eb8a-5f8b-be17-9b893d2db31b
-- title:
--   Rational q-adic Tate module of J₀(p) versus period lattice
-- statement:
--   Let $p$ and $q$ be primes. The Hecke algebra is $\mathbb{Z}[T_\ell : \ell \text{ prime}]$, realised as `HeckeAlg` $=$ `MvPolynomial Nat.Primes ℤ`, and `JZero p` is the degree-zero Picard group of the function field of the full modular curve of level $p$ over $\overline{\mathbb{Q}}$, equipped with the `HeckeAlg`-module structure `heckeModuleBar p` (which is the one induced by the ring homomorphism evaluating the variables at the bar-Hecke operators when these commute, and a degenerate structure otherwise). Write $\Lambda =$ `periodLattice p` for the $\mathbb{Z}$-span of the periods inside the $\mathbb{C}$-linear dual of the space of weight-two cusp forms on $\Gamma_0(p)$, with the `HeckeAlg`-action `periodLatticeHeckeEnd p` (the restriction of the Hecke operators when $\Lambda$ is stable under them, and a degenerate action otherwise). The assertion is that there exists a $\mathbb{Q}_q$-linear isomorphism
--   $$\Phi : \mathbb{Q}_q \otimes_{\mathbb{Z}_q} T_q(\mathrm{JZero}\,p) \ \xrightarrow{\ \sim\ }\ \mathbb{Q}_q \otimes_{\mathbb{Z}} \Lambda,$$
--   where $T_q(M)$ is the group of sequences $(x_n)$ in $M$ with $q^n x_n = 0$ and $q\,x_{n+1} = x_n$, such that for every $t \in$ `HeckeAlg` and every $v$ in the source, $\Phi$ intertwines the action of $t$ on the rational Tate module (`rationalHeckeRep`) with the $\mathbb{Q}_q$-base change of the endomorphism `periodLatticeHeckeEnd p t` of $\Lambda$. No relation between $p$ and $q$ is assumed.
--
--   This is the rational form of the Eichler–Shimura comparison identifying the $q$-adic Tate module of the Jacobian of $X_0(p)$ with the $q$-adic completion of the integral homology (period) lattice, compatibly with Hecke operators. It is used downstream in the construction of the Hecke-stable lattice data entering the study of inertia-fixed vectors in the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearEquiv_rationalTateModule_tensor_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped TensorProduct

set_option autoImplicit false

theorem ModularCurve.exists_linearEquiv_rationalTateModule_tensor_periodLattice
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    letI := heckeModuleBar p
    ∃ Φ : RationalTateModule q (JZero p) ≃ₗ[ℚ_[q]] (ℚ_[q] ⊗[ℤ] ↥(periodLattice p)),
      ∀ (t : HeckeAlg) (v : RationalTateModule q (JZero p)),
        Φ (rationalHeckeRep q (JZero p) t v) = ((periodLatticeHeckeEnd p t).baseChange ℚ_[q]) (Φ v) := by sorry
