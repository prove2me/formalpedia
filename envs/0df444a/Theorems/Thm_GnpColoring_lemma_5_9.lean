-- Prove2me | Theorems.Thm_GnpColoring_lemma_5_9
-- name    : GnpColoring.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:31.785191+00:00
-- url     : https://prove2.me/theorems/9ffb984b-bdc1-49ec-a2f6-bfa3de04ee9d
-- title:
--   Lemma 5.9 — nonemptiness and irreducibility
-- statement:
--   Let $G$ carry a valid block partition with singletons $S$, under the standing parameters of Section 3.1: $d>0$, $0<\eta<1/2$, $A>0$, $C>0$ and $\alpha=C\log d>1$, and suppose $\bar\Delta\ge2$ and $q\ge\lfloor\bar\Delta\rfloor+2$. Then:
--
--   1. $G$ has a proper $q$-colouring;
--   2. Glauber (single-site heat-bath) dynamics on proper $q$-colourings is irreducible;
--   3. the exact block dynamics is irreducible;
--   4. the Glauber generator $L_{\mathrm{Gl}}=\sum_vL_v$ has only constants in its kernel;
--   5. the block generator $L$ has only constants in its kernel.
--
--   This makes the uniform measure well defined and the Poincaré inequalities meaningful even though hubs may have degree larger than $q$.
--
--   Differences from the source:
--   - encoding: standing hypotheses stated once in Sections 3.1–3.2 (valid partition, $0<\eta<1/2$, $A,C>0$, $\alpha>1$) → explicit hypotheses; reason: they are the section's assumptions; nothing is added
--   - encoding: "its exact block dynamics are irreducible" → the jump chain `blockChain` is irreducible; reason: positive rescaling of rates does not change the possible transitions
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Lemma 5.9, p.54

import Mathlib
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_GnpColoring_blockChain
import Definitions.Def_GnpColoring_blockGen
import Definitions.Def_GnpColoring_KernelOnlyConstants
import Definitions.Def_GnpColoring_alphaW
import Definitions.Def_GnpColoring_deltaBar
import Definitions.Def_mm_transport
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **Lemma 5.9 (nonemptiness and irreducibility).** Suppose `G` has a valid block partition `S` and
`q ≥ ⌊Δ̄⌋ + 2`, with `Δ̄ ≥ 2`. Then `G` has a proper `q`-colouring; its single-site heat-bath (Glauber)
dynamics and its exact block dynamics are irreducible; and both generators, `L_Gl = Σ_v L_v` and
`L = Σ_s L_s + Σ_B L_B`, have only constants in their kernel.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Lemma 5.9, p.54: "Suppose G has a valid block partition and q ≥ ⌊Δ̄⌋ + 2, with Δ̄ ≥ 2. Then G
has a proper q-coloring. Its single-site heat-bath dynamics and its exact block dynamics are
irreducible, and both generators have only constants in their kernel."

**Formalization Note** The partition is valid for the standing parameters of Section 3.1. Glauber
dynamics is `MarkovMixing.coloringGlauber G q`; the exact block dynamics is `blockChain G q S`
(its jump chain); `L_Gl` is `SpinGirth5.lapSum µ V`. -/
theorem lemma_5_9 {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (d η A C D : ℝ)
    (S : Finset (Fin n)) (hd : 0 < d) (hη : 0 < η) (hη2 : η < 1 / 2) (hA : 0 < A) (hC : 0 < C)
    (hα : 1 < alphaW C d)
    (hS : IsValidPartition G d η A C D S) (hΔ : 2 ≤ deltaBar d η)
    (hq : ⌊deltaBar d η⌋₊ + 2 ≤ q) :
    Nonempty {σ : Fin n → Fin q // MarkovMixing.IsProperColoring G σ} ∧
      MarkovMixing.Irreducible (MarkovMixing.coloringGlauber G q) ∧
      MarkovMixing.Irreducible (blockChain G q S) ∧
      KernelOnlyConstants (MarkovMixing.properColoringDist G q) (SpinGirth5.lapSum (MarkovMixing.properColoringDist G q) univ) ∧
      KernelOnlyConstants (MarkovMixing.properColoringDist G q) (blockGen G q S) := by sorry

end GnpColoring
