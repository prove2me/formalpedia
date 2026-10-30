-- Prove2me | Theorems.Thm_OnlineCRS_Combine_chi_inter_product_bound
-- name    : OnlineCRS.Combine.chi_inter_product_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:27:35.262993+00:00
-- url     : https://prove2.me/theorems/c7e73eb1-f4da-4a89-b10c-6c830b162dec
-- title:
--   Product bound for the intersected family, with the families fixed
-- statement:
--   Let $x\in[0,1]^N$, $e\in N$, and let $\mathcal G_1,\mathcal G_2$ be any two families of subsets of $N$. Then
--   $$\Pr[\chi_e(R(x),\mathcal G_1,\mathcal G_1)]\cdot\Pr[\chi_e(R(x),\mathcal G_2,\mathcal G_2)]\ \le\ \Pr[\chi_e(R(x),\mathcal G_1\cap\mathcal G_2,\mathcal G_1\cap\mathcal G_2)],$$
--   the probabilities being over $R(x)$ only.
--
--   This is the displayed chain in the proof of Lemma 2.11 with the families $\mathcal F_{\pi^1,x}=\mathcal G_1$, $\mathcal F_{\pi^2,x}=\mathcal G_2$ held fixed: the event on the right is the conjunction of $\chi_e(R,\mathcal G_j,\mathcal G_1\cap\mathcal G_2)$, $j=1,2$, which are decreasing events, so the FKG inequality and the monotonicity of $\chi_e$ in its third argument give the bound. Averaging over the independent families gives Lemma 2.11.
--
--   Differences from the source:
--   - reading: the chain applies FKG to R(x) with the possibly random families F_{π¹,x}, F_{π²,x} inside the events → the chain for fixed families G₁, G₂ (conditioned on the families), probabilities over R(x) only; reason: for randomized OCRSs the page's FKG step is only valid conditionally on both families, which are independent of R(x) (Reading 2) and of each other (Reading 3); averaging is done in Lemma 2.11
--   - reading: chain ending in '≥ c1 · c2' → the product inequality only; the bound c₁ · c₂ is Lemma 2.11; reason: the last step uses selectability of π¹, π², which is the content of Lemma 2.11 (separate milestone)
--   - generalization: the down-closed families F_{π¹,x}, F_{π²,x} → arbitrary families G₁, G₂; reason: the step does not use down-closedness of the families; down-closed families are a special case
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, proof of Lemma 2.11 (unnumbered displayed chain), pp. 15–16

import Mathlib
import Definitions.Def_OnlineCRS_Combine_activeProb
import Definitions.Def_OnlineCRS_Combine_chi

namespace OnlineCRS.Combine

open Classical in
/-- **Per-realization product bound for the combined family.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, proof of Lemma 2.11, pp. 15–16 (unnumbered displayed chain):
"`Pr[χ_e(R(x), F_{π¹,x} ∩ F_{π²,x}, F_{π¹,x} ∩ F_{π²,x})]
= Pr[χ_e(R, F_{π¹,x}, F_{π¹,x} ∩ F_{π²,x}) · χ_e(R, F_{π²,x}, F_{π¹,x} ∩ F_{π²,x})]
≥ Pr[χ_e(R(x), F_{π¹,x}, F_{π¹,x} ∩ F_{π²,x})] · Pr[χ_e(R(x), F_{π²,x}, F_{π¹,x} ∩ F_{π²,x})] ≥ c₁ · c₂`."

For `x ∈ [0,1]^N`, every two families `G₁, G₂` and every `e`,
`Pr[χ_e(R(x), G₁, G₁)] · Pr[χ_e(R(x), G₂, G₂)] ≤ Pr[χ_e(R(x), G₁ ∩ G₂, G₁ ∩ G₂)]`.

**Formalization Note.** Reading (proof gap): the page applies FKG to `R(x)` while the families
`F_{πʲ,x}` may be random; this is the chain with the families fixed (conditioned on), which with
Reading 2 (families independent of `R(x)`) and Reading 3 (the two families independent) gives
Lemma 2.11 after averaging. The families are arbitrary (they need not be down-closed); the
paper's case is down-closed families. The final `≥ c₁ · c₂` of the chain is Lemma 2.11. -/
theorem chi_inter_product_bound {N : Type*} [Fintype N] [DecidableEq N] {x : N → ℝ}
    (hx : x ∈ Set.Icc (0 : N → ℝ) 1) (G₁ G₂ : Finset (Finset N)) (e : N) :
    (∑ A : Finset N, activeProb x A * (if chi e A G₁ G₁ then 1 else 0)) *
        (∑ A : Finset N, activeProb x A * (if chi e A G₂ G₂ then 1 else 0)) ≤
      ∑ A : Finset N, activeProb x A * (if chi e A (G₁ ∩ G₂) (G₁ ∩ G₂) then 1 else 0) := by sorry

end OnlineCRS.Combine
