-- Prove2me | Theorems.Thm_MastSail_Monotone_lemma_OA3
-- name    : MastSail.Monotone.lemma_OA3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:28.435554+00:00
-- url     : https://prove2.me/theorems/44f606fc-ae05-441f-8927-b4bf9a9d48cc
-- title:
--   Lemma OA3, p. oa4 — the inventory, survival and demand likelihood ratios are nonincreasing and nonconstant
-- statement:
--   Assume the standing assumptions of the model: $0<\bar I<\bar Q$, positive continuous densities $f(\cdot\mid e^L_o)$, $f(\cdot\mid e^H_o)$ on $[0,\bar I]$ and $g(\cdot\mid e^L_m)$, $g(\cdot\mid e^H_m)$ on $[0,\bar Q]$, and the monotone likelihood ratio property (1). Then:
--
--   1. the ratios
--   $$\frac{f(i\mid e^L_o)}{f(i\mid e^H_o)}\qquad\text{and}\qquad\frac{1-G(i\mid e^L_m)}{1-G(i\mid e^H_m)}$$
--   are nonincreasing in $i\in[0,\bar I]$;
--   2. the ratio $g(s\mid e^L_m)/g(s\mid e^H_m)$ is nonincreasing in $s\in[0,\bar Q]$;
--   3. if $f(\cdot\mid e^L_o)\ne f(\cdot\mid e^H_o)$ somewhere on $[0,\bar I]$, the inventory ratio is not constant on $[0,\bar I]$;
--   4. if $g(\cdot\mid e^L_m)\ne g(\cdot\mid e^H_m)$ somewhere on $[0,\bar Q]$, the survival ratio is not constant on $[0,\bar I]$ and the demand ratio is not constant on $[0,\bar Q]$.
--
--   The survival-ratio monotonicity (the likelihood-ratio order implies the hazard-rate order) is what makes the stockout ratio function $\varphi^{SO}$ monotone, and so gives the mast its shape.
--
--   **Formalization Note** The paper prints the second ratio's denominator as $1-G(i\mid e^L_m)$, which would make it identically $1$ and contradict "nonconstant"; it is read as $1-G(i\mid e^H_m)$, matching (OA7). "Nonconstant" needs the two distributions to differ, which the paper leaves implicit; it is stated under that hypothesis. Part (ii) is taken on the demand support $[0,\bar Q]$: on $[0,\bar I]$ alone the demand ratio may be constant although the densities differ.
-- source:
--   Dai, Ke & Ryan, SSRN 3235866, p. oa4, Lemma OA3 (in the proof of Proposition 1)

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone
theorem lemma_OA3 (M : Model) (hM : M.Standing) :
    (AntitoneOn (fun i => M.fL i / M.fH i) (Set.Icc 0 M.Ibar) ∧
      AntitoneOn (fun i => (1 - cdf M.gL i) / (1 - cdf M.gH i)) (Set.Icc 0 M.Ibar)) ∧
    AntitoneOn (fun s => M.gL s / M.gH s) (Set.Icc 0 M.Qbar) ∧
    ((∃ x ∈ Set.Icc 0 M.Ibar, M.fL x ≠ M.fH x) →
      ∃ a ∈ Set.Icc 0 M.Ibar, ∃ b ∈ Set.Icc 0 M.Ibar, M.fL a / M.fH a ≠ M.fL b / M.fH b) ∧
    ((∃ x ∈ Set.Icc 0 M.Qbar, M.gL x ≠ M.gH x) →
      (∃ a ∈ Set.Icc 0 M.Ibar, ∃ b ∈ Set.Icc 0 M.Ibar,
        (1 - cdf M.gL a) / (1 - cdf M.gH a) ≠ (1 - cdf M.gL b) / (1 - cdf M.gH b)) ∧
      (∃ a ∈ Set.Icc 0 M.Qbar, ∃ b ∈ Set.Icc 0 M.Qbar, M.gL a / M.gH a ≠ M.gL b / M.gH b)) := by sorry
end MastSail.Monotone
