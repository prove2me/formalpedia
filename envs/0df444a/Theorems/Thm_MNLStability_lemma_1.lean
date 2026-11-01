-- Prove2me | Theorems.Thm_MNLStability_lemma_1
-- name    : MNLStability.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:37.399318+00:00
-- url     : https://prove2.me/theorems/78edf00f-804e-4bf1-a338-41e3ab67c7cb
-- title:
--   Lemma 1 — deleting a unit raises every remaining unit's consumption probability
-- statement:
--   Let $U$ be an inventory vector, $d$ a product with $U_d\ge1$, and $U^{-d}=U-e_d$ the vector obtained by deleting one unit of $d$. Then for every product $i$ and every unit index $1\le u\le U^{-d}_i$,
--
--   $$\Pr\bigl[I^{U^{-d}}_{(i,u)}=1\bigr]\ \ge\ \Pr\bigl[I^{U}_{(i,u)}=1\bigr],$$
--
--   where $I^U_{(i,u)}$ indicates that unit $(i,u)$ is consumed when the initial vector is $U$, and the number of customers $M$ is random with a finitely supported law.
--
--   Deletions can only help the remaining units; the lemma drives the item 1 bounds of Lemmas 7 and 9 and the proof of Lemma 2. The paper cites it from Aouad et al. (2018b, Claim 10) without proof.
--
--   Differences from the source:
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 1, p.12

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_prob

namespace MNLStability

/-- **Lemma 1** (SSRN:3498325, p.12; cited from Aouad et al. 2018b, Claim 10). Let `U^{−d} = U − e_d`
be obtained from `U` by deleting one unit of a stocked product `d`. For every product `i` and every
`u ≤ U_i^{−d}`, `Pr[I^{U^{−d}}_{(i,u)} = 1] ≥ Pr[I^U_{(i,u)} = 1]`.

**Formalization Note.** Unit indices start at `1`; `unitProb` mixes over the law `pM` of `M`. -/
theorem lemma_1 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (U : Fin n → ℕ) (d : Fin n) (hd : 0 < U d) (i : Fin n) (u : ℕ) (hu1 : 1 ≤ u)
    (hu : u ≤ (U - Pi.single d 1 : Fin n → ℕ) i) :
    unitProb wts pM U i u ≤ unitProb wts pM (U - Pi.single d 1) i u := by sorry

end MNLStability
