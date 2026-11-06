-- Prove2me | Theorems.Thm_GnpColoring_lemma_3_4
-- name    : GnpColoring.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:31.881866+00:00
-- url     : https://prove2.me/theorems/11a1a5c2-adc2-4232-ae39-51cd0589c08e
-- title:
--   Lemma 3.4 — $\tilde L^2-\kappa q\tilde L\succeq0$ implies $\mathrm{gap}(L)\ge\kappa$
-- statement:
--   Let $G$ carry a valid block partition with singletons $S$ and blocks $\mathcal B$ (Definition 3.2), under the standing parameters of Section 3.1: $d>0$, $0<\eta<1/2$, $A>0$, $C>0$ and $\alpha=C\log d>1$. Let $\mu$ be the uniform measure on proper $q$-colourings, $L=\sum_{s}L_s+\sum_BL_B$ the block generator, $\tilde L=\sum_s a_sL_s+q\sum_BL_B$ the accelerated generator and $\kappa\in\mathbb R$. If
--
--   $$\langle f,(\tilde L^2-\kappa q\tilde L)f\rangle_\mu\ge0\quad\text{for every }f$$
--
--   and the kernel of $L$ consists only of constants, then $\mathrm{gap}(L)\ge\kappa$, i.e. $\kappa\,\mathrm{Var}_\mu[f]\le\langle f,Lf\rangle_\mu$ for every $f$.
--
--   This is the step that turns the Bochner-type inequality of Section 3 into a spectral gap for the block dynamics.
--
--   Differences from the source:
--   - encoding: standing hypotheses stated once in Sections 3.1–3.2 (valid partition, $0<\eta<1/2$, $A,C>0$, $\alpha>1$) → explicit hypotheses; reason: they are the section's assumptions; nothing is added
--   - encoding: $\mathrm{gap}(L)\ge\kappa$, i.e. $\mathrm{Var}_\mu f\le\kappa^{-1}\langle f,Lf\rangle_\mu$ → $\kappa\langle f,f\rangle_\mu\le\langle f,Lf\rangle_\mu$ for centred $f$; reason: $L$ kills constants on the support of $\mu$, so the two forms agree
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Lemma 3.4, p.16

import Mathlib
import Definitions.Def_GnpColoring_bochnerOp
import Definitions.Def_GnpColoring_blockGen
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_GnpColoring_KernelOnlyConstants
import Definitions.Def_GnpColoring_alphaW
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **Lemma 3.4 (Bochner inequality ⇒ spectral gap).** If `L̃² − κqL̃ ⪰ 0` and the kernel of the
block generator `L` consists only of constants, then `gap(L) ≥ κ`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Lemma 3.4, p.16: "If L̃² − κqL̃ ⪰ 0 and the kernel of L consists only of constants, then
gap(L) ≥ κ."

**Formalization Note** The setting is Section 3.2 (p.15: "Assume that G admits a valid block
partition"), with the standing parameters of Section 3.1 (`0 < η < 1/2`, `A > 0`, `C > 0`,
`α = C log d > 1`). `A ⪰ B` is `⟨f, (A − B)f⟩_µ ≥ 0` for every `f` (p.13). `gap(L) ≥ κ` is the
Poincaré inequality `κ Var_µ[f] ≤ ⟨f, Lf⟩_µ` (p.14), written as `SpinGirth5.PoincareIneq` on
centred `f`. -/
theorem lemma_3_4 {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (d η A C D κ : ℝ)
    (S : Finset (Fin n)) (hd : 0 < d) (hη : 0 < η) (hη2 : η < 1 / 2) (hA : 0 < A) (hC : 0 < C)
    (hα : 1 < alphaW C d)
    (hS : IsValidPartition G d η A C D S)
    (hBochner : ∀ f : (Fin n → Fin q) → ℝ,
      0 ≤ MarkovMixing.innerPi (MarkovMixing.properColoringDist G q) f (bochnerOp G q S κ f))
    (hker : KernelOnlyConstants (MarkovMixing.properColoringDist G q) (blockGen G q S)) :
    SpinGirth5.PoincareIneq (MarkovMixing.properColoringDist G q) (blockGen G q S) κ := by sorry

end GnpColoring
