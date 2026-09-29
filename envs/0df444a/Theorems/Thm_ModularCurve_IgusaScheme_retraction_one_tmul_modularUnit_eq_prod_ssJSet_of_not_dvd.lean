-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd
-- name    : ModularCurve.IgusaScheme.retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/793de93b-170a-54fd-9935-02ac44810862
-- title:
--   Ogg's unit on the two components of X₀(Np) mod p
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime with $p\nmid N$, and write $\mathbb Z_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ consisting of the rationals whose denominator is coprime to $p$. Let $\kappa$ be an algebraically closed field of characteristic $p$ equipped with a $\mathbb Z_{(p)}$-algebra structure. For a level $M$, `chartAlgFin M p` is the $\mathbb Z_{(p)}$-subalgebra of the field `modularFunctionFieldFull M` $\subset$ `LaurentSeries ℚ` of elements integral over $\mathbb Z_{(p)}[j]$, $j$ being the $q$-expansion `jFull M`, with distinguished element `jChartFin M p` $=j$. Assume given: a $\mathbb Z_{(p)}$-algebra map $\iota$ from `chartAlgFin N p` to `chartAlgFin (N*p) p` which preserves the underlying Laurent series; a $\mathbb Z_{(p)}$-algebra automorphism $w$ of `chartAlgFin (N*p) p` induced by `atkinLehnerInvolutionFull N p`, the $\mathbb Q$-automorphism of `modularFunctionFieldFull (N*p)` interchanging the $q$-expansions of $j(d\tau)$ and $j(dp\tau)$ for every divisor $d$ of $N$ (chosen if such an automorphism exists); a $\kappa$-algebra map $\sigma_0:\kappa\otimes_{\mathbb Z_{(p)}}$`chartAlgFin (N*p) p`$\to\kappa\otimes_{\mathbb Z_{(p)}}$`chartAlgFin N p` which is a retraction of $\mathrm{id}_\kappa\otimes\iota$, i.e. $\sigma_0((\mathrm{id}\otimes\iota)z)=z$ for all $z$; and an element $v$ of `chartAlgFin (N*p) p` whose Laurent series is `modularUnitSeries p` $=\Delta(q)\,\Delta(q^p)^{-1}$. Then five assertions hold. (1) $\sigma_0(1\otimes w(v))=0$. (2) If $p\ge 5$, then for every finset $S\subset\kappa$ whose members are exactly the elements of `ssJSet p κ` — the set of $a\in\kappa$ such that every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $a$ has no nonzero $p$-torsion affine point — one has $\sigma_0(1\otimes v)=\prod_{a\in S}(1\otimes j-a\otimes 1)^{12/ e_a}$, with natural-number division and $e_a=$ `jWidth a` equal to $3$ for $a=0$, $2$ for $a=1728$ and $1$ otherwise. (3) For every prime ideal $\mathfrak p$ of $\kappa\otimes$`chartAlgFin N p`, $\sigma_0(1\otimes v)\in\mathfrak p$ if and only if $1\otimes j-a\otimes 1\in\mathfrak p$ for some $a\in$ `ssJSet p κ`. (4) $\sigma_0(1\otimes v)\ne 0$. (5) The kernels of $\sigma_0$ and of $\mathrm{id}_\kappa\otimes w$ followed by $\sigma_0$ are both minimal primes of $\kappa\otimes_{\mathbb Z_{(p)}}$`chartAlgFin (N*p) p`, and they are distinct.
--
--   This is the ring-theoretic form of the classical description of the fibre of $X_0(Np)$ at $p$ by two copies of $X_0(N)_\kappa$ crossing at the supersingular points: Ogg's modular unit $\Delta(\tau)/\Delta(p\tau)$ vanishes identically on the copy exchanged by $w_p$, while on the copy cut out by the retraction $\sigma_0$ it becomes Deuring's supersingular polynomial, whose zero locus is exactly the supersingular $j$-invariants. It supplies the enumeration of the nodes of the Deligne–Rapoport fibre used in the level-lowering part of the argument, and is cited by the statements identifying places of points of the mod $p$ fibre and by the results extracting supersingular $j$-invariants from pairs of minimal primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
open ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

    (ι : ↥(chartAlgFin N p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))

    (σ₀ : κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) →ₐ[κ]
        κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)

    (v : ↥(chartAlgFin (N * p) p))
    (hv : ((v : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) = modularUnitSeries p) :

    σ₀ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (w v : ↥(chartAlgFin (N * p) p))) = 0 ∧

    (5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      σ₀ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] v) =
        ∏ a ∈ S, ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p -
          a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin N p))) ^ (12 / jWidth a)) ∧

    (∀ 𝔭 : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p)), 𝔭.IsPrime →
      (σ₀ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] v) ∈ 𝔭 ↔
        ∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p -
          a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin N p)) ∈ 𝔭)) ∧

    σ₀ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] v) ≠ 0 ∧

    (RingHom.ker σ₀ ∈ minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) ∧
      RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)) ∈
        minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) ∧
      RingHom.ker σ₀ ≠ RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom))) := by sorry
