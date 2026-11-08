-- Prove2me | Theorems.Thm_MaxCompForest_eq_3_2_transfer_current
-- name    : MaxCompForest.eq_3_2_transfer_current
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:26.46648+00:00
-- url     : https://prove2.me/theorems/47d211a2-b6d8-492e-b7f4-4c873c5cb345
-- title:
--   Eq. (3.2), (4.5) — transfer-current identity $P(F\subseteq T)=\Phi_G(F)/\tau_c(G)=\det K_F$
-- statement:
--   Let $G=(V,E)$ be a connected loopless multigraph with positive conductances $c_e$, and let $T$ be a spanning tree sampled with probability $c(T)/\tau_c(G)$. Let $K=C_E^{1/2}B^{\top}L_G^{+}BC_E^{1/2}$ be the transfer-current kernel. For every set $F$ of edge labels,
--   $$
--   P(F\subseteq T)=\frac{\Phi_G(F)}{\tau_c(G)}=\det K_F .
--   $$
--   If $F$ is a forest then
--   $$
--   \Phi_G(F)=c(F)\,\tau_c(G/F),
--   $$
--   and if $F$ is cyclic then $\Phi_G(F)=0$ and $\det K_F=0$.
--
--   This identity makes maximum-completion forest selection a determinant-maximization problem on an edge-indexed projection, and every later step of the algorithm rests on it. The paper cites it (Burton–Pemantle, Lyons, Chaiken).
--
--   Differences from the source:
--   - encoding: $B$ is vertices × edges → the published `incidence` is edges × vertices, so it plays the role of $B^\top$; reason: the same Laplacian and the same kernel
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.1)–(3.2) p.14, (4.5) p.27

import Mathlib
import Definitions.Def_MaxCompForest_inclProb
import Definitions.Def_MaxCompForest_K
import Definitions.Def_MaxCompForest_onLabels
import Definitions.Def_MaxCompForest_IsForest
import Definitions.Def_MaxCompForest_contract
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Eq. (3.2) with (4.5) and the product formula of (3.1)**: `P(F ⊆ T) = Φ_G(F)/τ_c(G) = det K_F` for every label set of a connected
loopless multigraph; `Φ_G(F) = c(F) τ_c(G/F)` for a forest; completion score and determinant vanish for a
cyclic set.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.1)–(3.2) p.14, (4.5) p.27.

**Formalization Note.** Parallel labels are allowed (p.15). The first equality is the definition of
`inclProb`. -/
theorem eq_3_2_transfer_current {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) (F : Finset E) :
    inclProb G F = (onLabels (K G) F).det ∧
      (IsForest G F → Phi G F = weight G F * tau (contract G F)) ∧
      (¬ IsForest G F → Phi G F = 0 ∧ (onLabels (K G) F).det = 0) := by sorry

end MaxCompForest
