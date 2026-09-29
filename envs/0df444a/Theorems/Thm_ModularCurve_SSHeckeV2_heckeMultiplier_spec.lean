-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_heckeMultiplier_spec
-- name    : ModularCurve.SSHeckeV2.heckeMultiplier_spec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/60080ed1-24a8-5200-a66b-0c1a8b090e9e
-- title:
--   The Hecke multiplier satisfies its defining differential identity
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $K$ be an algebraically closed field of characteristic $p$, let $N \ge 1$ be an integer whose image in $K$ is nonzero, and let $\ell$ be a prime not dividing $N$ whose image in $K$ is nonzero. Write $F = K(j(\mathsf q), j(\mathsf q^{N})) \subseteq K(\!(\mathsf q)\!)$ for the field `modularFunctionFieldC K N` generated over $K$ by the $j$-series `jqModC K` and its $N$-fold $\mathsf q$-substitution, and $R$ for the $\ell$-degeneracy roof `charLDegeneracyRoof K N ℓ`, the subfield generated over $K$ by $j(\mathsf q), j(\mathsf q^{N}), j(\mathsf q^{\ell}), j(\mathsf q^{N\ell})$. Let $\alpha \colon F \to R$ be the inclusion `heckeAlphaC`, used to view $R$ as an $F$-algebra, and let $\beta \colon F \to R$ be the map `heckeBetaC` induced by $\mathsf q \mapsto \mathsf q^{\ell}$. With $\bar\jmath =$ `jGeomGen K N` the element $j(\mathsf q)$ of $F$, the assertion is the identity $$d_{R/K}(\beta\bar\jmath) \;=\; h \cdot \alpha^{*}\bigl(d_{F/K}\bar\jmath\bigr)$$ in $\Omega_{R/K}$, where $h =$ [`ModularCurve.heckeMultiplier N K ℓ`](def/ModularCurve_SSHeckeV2.html#L20) is the element of $R$ chosen (by unrestricted choice) to satisfy exactly this equation; thus the theorem says such an $h$ exists, so that the choice is specified.
--
--   The element $h$ is the multiplier of the geometric Hecke correspondence at $\ell$ on the modular curve in characteristic $p$, comparing the pull-backs of $dj$ along the two degeneracy maps from the roof; as a $\mathsf q$-series it is $\ell\,(\theta\bar\jmath)(\mathsf q^{\ell})/\theta\bar\jmath$. It underlies the construction of Hecke operators on weight-$2m$ functions and mod $p$ eigenforms, and is cited in the study of mod $p$ eigenvectors in Riemann–Roch spaces at the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_heckeMultiplier_spec.lean

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.heckeMultiplier_spec (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
    haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ);
    KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
      = ModularCurve.heckeMultiplier N K ℓ • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
          (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) := by sorry
