-- Prove2me | Theorems.Thm_GnpColoring_theorem_5_10
-- name    : GnpColoring.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:47.462114+00:00
-- url     : https://prove2.me/theorems/2caa93be-fadd-4807-b88f-b6a9ce5cd977
-- title:
--   Theorem 5.10 — block-to-single-site comparison
-- statement:
--   Let $G$ carry a valid block partition (under the standing parameters of Section 3.1: $d>0$, $0<\eta<1/2$, $A>0$, $C>0$ and $\alpha=C\log d>1$), let $\mu$ be the uniform measure on the nonempty set of proper $q$-colourings, $\gamma>0$ and $T_*\ge1$. Suppose the block dynamics satisfies $\mathrm{Var}_\mu[f]\le\gamma^{-1}\langle f,Lf\rangle_\mu$ for every $f$, and $\tau_{\mathrm{rel}}(B,\tau)\le T_*$ for every block $B$ and feasible $\tau$. Then
--
--   $$\mathrm{gap}(L_{\mathrm{Gl}})\ge\frac{\gamma}{T_*},\qquad \mathrm{gap}(I-P_{\mathrm{Gl}})\ge\frac{\gamma}{nT_*},\tag{5.11}$$
--
--   where $L_{\mathrm{Gl}}=\sum_vL_v$ and $P_{\mathrm{Gl}}=n^{-1}\sum_v(I-L_v)$ is discrete-time Glauber dynamics.
--
--   Differences from the source:
--   - encoding: standing hypotheses stated once in Sections 3.1–3.2 (valid partition, $0<\eta<1/2$, $A,C>0$, $\alpha>1$) → explicit hypotheses; reason: they are the section's assumptions; nothing is added
--   - encoding: $\mathrm{Var}_\mu[f]\le\gamma^{-1}\langle f,Lf\rangle_\mu$; gaps → Poincaré inequalities on centred $f$; reason: generators kill constants on the support of $\mu$
--   - encoding: "the uniform within-block relaxation bound is $T_*$" → $T_*\ge1$ and $\tau_{\mathrm{rel}}(B,\tau)\le T_*$ for all blocks and feasible $\tau$; reason: $T_*=\max\{1,\sup\tau_{\mathrm{rel}}\}$ (p.44)
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Theorem 5.10, Eq. (5.11), p.55

import Mathlib
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_GnpColoring_blockGen
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_IsFeasible
import Definitions.Def_GnpColoring_RelaxBound
import Definitions.Def_GnpColoring_alphaW
import Definitions.Def_mm_transport
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **Theorem 5.10 (block-to-single-site comparison).** Suppose the block dynamics satisfies
`Var_µ[f] ≤ γ⁻¹⟨f, Lf⟩_µ` for every `f`, and the uniform within-block relaxation bound is `T∗`. Then
`gap(L_Gl) ≥ γ/T∗`, and for the discrete-time chain `P_Gl = n⁻¹ Σ_v (I − L_v)`, `gap(I − P_Gl) ≥ γ/(nT∗)`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Theorem 5.10, Eq. (5.11), p.55.

**Formalization Note** `µ` is the uniform law on the nonempty set of proper `q`-colourings (p.54:
"Let µ be the uniform measure on the nonempty space of proper q-colorings of G"); `L` is the block
generator of a valid partition (standing parameters of Section 3.1). "The uniform within-block
relaxation bound is `T∗`" is `T∗ ≥ 1` (p.44: `T∗ := max{1, sup τ_rel}`) and `τ_rel(B, τ) ≤ T∗` for every
block and feasible `τ`. Gaps are Poincaré inequalities (`SpinGirth5.PoincareIneq`); `I − P_Gl` acts by
`f ↦ f − n⁻¹ Σ_v P_v f` with `P_v` the heat-bath update at `v`. -/
theorem theorem_5_10 {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (d η A C D : ℝ)
    (S : Finset (Fin n)) (hd : 0 < d) (hη : 0 < η) (hη2 : η < 1 / 2) (hA : 0 < A) (hC : 0 < C)
    (hα : 1 < alphaW C d)
    (hS : IsValidPartition G d η A C D S)
    (hne : Nonempty {σ : Fin n → Fin q // MarkovMixing.IsProperColoring G σ})
    (γ Tstar : ℝ) (hγ : 0 < γ) (hT : 1 ≤ Tstar)
    (hgap : SpinGirth5.PoincareIneq (MarkovMixing.properColoringDist G q) (blockGen G q S) γ)
    (hrel : ∀ B ∈ blocks G S, ∀ x : Fin n → Fin q, IsFeasible G q B x → RelaxBound G q B x Tstar) :
    SpinGirth5.PoincareIneq (MarkovMixing.properColoringDist G q) (SpinGirth5.lapSum (MarkovMixing.properColoringDist G q) univ) (γ / Tstar) ∧
      SpinGirth5.PoincareIneq (MarkovMixing.properColoringDist G q)
        (fun f x => f x - (n : ℝ)⁻¹ * ∑ v, SpinGirth5.heatBath (MarkovMixing.properColoringDist G q) v f x)
        (γ / (n * Tstar)) := by sorry

end GnpColoring
