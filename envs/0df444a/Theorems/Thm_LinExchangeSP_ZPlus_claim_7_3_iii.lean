-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_claim_7_3_iii
-- name    : LinExchangeSP.ZPlus.claim_7_3_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:37.803635+00:00
-- url     : https://prove2.me/theorems/574e856b-e7a4-4d6d-8f1f-dee0e50ec8aa
-- title:
--   Claim 7.3(iii), p. 19 — for i ∈ T₃, the row Mᵢ is a linear combination of the rows M_h, h ∈ Dᵢ ∖ {i}
-- statement:
--   Let $M \in \mathcal{Z}_+(t,t)$ have all diagonal entries positive, let $([t],H)$ be the digraph with an arc $ij$ whenever $M_{ij} < 0$, let $D_i$ be the set of vertices reachable from $i$ (including $i$), and let $T_3$ be the set of $i$ with at least two outgoing arcs such that the rows $\{M_h : h \in D_i\}$ have rank less than $|D_i|$. If $i \in T_3$, then
--
--   $$M_i \in \operatorname{span}_{\mathbb{Q}}\{M_h : h \in D_i \setminus \{i\}\}.$$
--
--   In the proof of Theorem 6.4 this is used, for $i \in T_3$, to conclude $M_i q = 0$ from $M_h q = 0$ for $h \in D_i\setminus\{i\}$.
--
--   **Formalization Note** The positive diagonal is the standing assumption of §7 (p. 16, "We further assume that all diagonal entries are strictly positive"). Rows are vectors in $\mathbb{Q}^t$ and the span is taken over $\mathbb{Q}$, which matches the rank over $\mathbb{Q}$ in the definition of $T_3$.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 19, Claim 7.3(iii)

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace LinExchangeSP.ZPlus

/-- Claim 7.3(iii) (p. 19), in the setting of §7 (`M ∈ Z₊(t, t)`, positive diagonal): if `i ∈ T₃`,
the row `M_i` is a linear combination of the rows `M_h`, `h ∈ Dᵢ \ {i}`. -/
theorem claim_7_3_iii {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (i : Fin t) (hi : InT3 M i) :
    M i ∈ Submodule.span ℚ ((fun h => M h) '' ((D M i : Set (Fin t)) \ {i})) := by sorry

end LinExchangeSP.ZPlus
