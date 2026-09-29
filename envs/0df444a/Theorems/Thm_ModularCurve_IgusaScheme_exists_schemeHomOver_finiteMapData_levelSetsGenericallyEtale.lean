-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_schemeHomOver_finiteMapData_levelSetsGenericallyEtale
-- name    : ModularCurve.IgusaScheme.exists_schemeHomOver_finiteMapData_levelSetsGenericallyEtale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/dd425d0a-4744-52b0-bdc5-aeef773e5436
-- title:
--   Finite-map data of arbitrarily large degree on the Igusa scheme
-- statement:
--   Fix a level $N$ with $N \neq 0$ and a prime $\ell$ with $\ell \nmid N$, and let $\mathbb{Z}_{(\ell)}$ denote the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. Write $C =$ [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255), the pushout of the two chart maps `fFin N ℓ` and `fInf N ℓ`, and $c =$ `igusaTo N ℓ` for the structure morphism $C \to \operatorname{Spec}\mathbb{Z}_{(\ell)}$ obtained by descending the two chart algebras. The assertion is that there exists a section $\varepsilon$ of $c$, i.e. a morphism $\operatorname{Spec}\mathbb{Z}_{(\ell)} \to C$ whose composite with $c$ is the identity, such that for every $m_0 \in \mathbb{N}$ there is a datum $\mathfrak{F}$ of type `SmoothProperCurve.FiniteMapData c ε` with $m_0 \le \mathfrak{F}.m$ and satisfying $\mathfrak{F}$`.LevelSetsGenericallyEtale`. Unfolding, such a datum consists of affine opens $U, V \subseteq C$ with $U \sqcup V = C$, sections $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$, and a natural number $m$, such that: $U$ is exactly the complement of the image of $\varepsilon$; $U \cap V$ equals both the basic open set of $f$ and that of $g$; the restrictions of $f$ and $g$ to $U \cap V$ have product $1$; $\Gamma(C,U)$ is a finite module over the image of $\mathbb{Z}_{(\ell)}[T] \to \Gamma(C,U)$, $T \mapsto f$, and likewise $\Gamma(C,V)$ over $\mathbb{Z}_{(\ell)}[T] \to \Gamma(C,V)$, $T \mapsto g$ (the algebra structures coming from $c$); and for every local $\mathbb{Z}_{(\ell)}$-algebra $S$ and every $s \in S$ the level set ring $S \otimes_{\mathbb{Z}_{(\ell)}} \Gamma(C,U) / (1 \otimes f - s \otimes 1)$ is a finite free $S$-module of rank exactly $m$. The further property `LevelSetsGenericallyEtale` says that there is a polynomial $D \in \mathbb{Z}_{(\ell)}[T]$ having at least one unit coefficient such that for every local $\mathbb{Z}_{(\ell)}$-algebra $S$ whose structure map is a local homomorphism and every $s \in S$ with $D(s)$ a unit, the level set ring above is étale over $S$.
--
--   This packages the classical statement that, for $\ell \nmid N$, the modular curve of level $N$ over $\mathbb{Z}_{(\ell)}$ admits finite flat maps to the projective line of arbitrarily large degree with pole divisor concentrated at a chosen section (the cusp), with level sets that are étale away from a divisor defined by one polynomial. It is the concrete input to the relative-Jacobian and Néron-model interface for the Igusa scheme, and is used by [`ModularCurve.IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo`](thm.html#ModularCurve.IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo) and by [`ModularCurve.exists_smoothProperModel_jZero_relCurve_finiteMapData_ratCurveModel`](thm.html#ModularCurve.exists_smoothProperModel_jZero_relCurve_finiteMapData_ratCurveModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_schemeHomOver_finiteMapData_levelSetsGenericallyEtale.lean

import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra ModularCurve
  ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_schemeHomOver_finiteMapData_levelSetsGenericallyEtale
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    ∃ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) (igusaTo N ℓ),
      ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData (igusaTo N ℓ) ε,
        m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale := by sorry
