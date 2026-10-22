-- Prove2me | Theorems.Thm_GittinsUCB_Patient_lemma_2
-- name    : GittinsUCB.Patient.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:26.943533+00:00
-- url     : https://prove2.me/theorems/f3bb6033-e564-49c4-be57-980992a54d48
-- title:
--   Lemma 2 — square-root perturbation
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ satisfy $|f(x)|=o(\sqrt{x})$ as $x\to\infty$. Then
--
--   $$\sqrt{x+f(x)}=\sqrt{x}+o(1)\qquad(x\to\infty).$$
--
--   This estimate is used when lower-order corrections enter the square roots in the index bounds.
--
--   **Formalization Note** The paper prints $f:\mathbb R_+\to\mathbb R_+$, but its later application to $h(\gamma)$ requires negative values. The real-valued version records that intended domain; $\sqrt{\cdot}$ is Lean's total real square root, and the little-o premise controls the eventual radicand.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 3, Lemma 2

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Lemma 2: square-root perturbations. -/
theorem lemma_2 (f : ℝ → ℝ)
    (hf : (fun x : ℝ => |f x|) =o[atTop] Real.sqrt) :
    Tendsto (fun x : ℝ => Real.sqrt (x + f x) - Real.sqrt x) atTop (nhds 0) := by sorry

end GittinsUCB.Patient
