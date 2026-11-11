-- Prove2me | Theorems.Thm_LindbladShallow_lemma_3_3
-- name    : LindbladShallow.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:38.758783+00:00
-- url     : https://prove2.me/theorems/88082ff8-df20-4f0f-960a-f35eeecbd9a6
-- title:
--   Lemma 3.3 — weighted connected-set bound
-- statement:
--   Let $B$ be a finite set of labels with finite supports $X_b$ and weights $\omega_b\ge0$, with overlap graph $b\sim c\iff X_b\cap X_c\ne\emptyset$, and let $S,C\subseteq B$. Put
--   $$d_w=\sup_{b\in B}\sum_{c:\,X_c\cap X_b\ne\emptyset}\omega_c,\qquad W_S=\sum_{b\in S}\omega_b,$$
--   and assume every connected set meeting both $S$ and $C$ has at least $m_*\ge1$ vertices. If $6d_w<1$, the total activity $\sum_F\prod_{b\in F}\omega_b$ of all connected sets $F$ joining the source $S$ to the restriction boundary $C$ is at most
--   $$\zeta=\frac{W_S(6d_w)^{m_*-1}}{1-6d_w}.$$
--
--   This polymer-type bound is the combinatorial core of the shared-environment locality estimate (Theorem 3.4).
--
--   Differences from the source:
--   - generalization: occurrence labels with ω_b = 64hλ_b → any finite label set with arbitrary supports and weights ω_b ≥ 0; reason: the bound uses only the overlap structure and nonnegativity; Theorem 3.4's setting is a case
--   - encoding: an integer m∗ → m∗ : ℕ with 1 ≤ m∗; reason: every crossing set has a vertex, and the case m∗ = 0 follows from m∗ = 1
--   - encoding: sup_b → a real supremum over the finite set B (0 when B is empty); reason: the maximum for nonempty B; for empty B every sum vanishes
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma 3.3, p.16 (definitions of d_w, W_S, crossing sets on p.16; overlap graph p.14)

import Mathlib
import Definitions.Def_LindbladShallow_activity

namespace LindbladShallow

/-- **Lemma 3.3** (Weighted connected-set bound; arXiv:2610.05362, held version
sha256 8f4637ef…, p.16). Let `B` be a finite label set with supports `X_b` and activities
`ω_b ≥ 0`, overlap graph `b ∼ c ⟺ X_b ∩ X_c ≠ ∅`, source and cut sets `S, C ⊆ B`,
`d_w := sup_b Σ_{c : X_c ∩ X_b ≠ ∅} ω_c`, `W_S := Σ_{b ∈ S} ω_b`, and assume every connected
crossing set (meeting `S` and `C`) has at least `m∗` vertices. If `6d_w < 1`, the total activity
`Σ_F ∏_{b ∈ F} ω_b` of all connected crossing sets is at most
`ζ = W_S (6d_w)^{m∗−1} / (1 − 6d_w)`.

**Formalization Note** Stated for an arbitrary weighted support family (the paper's application is
`ω_b = 64hλ_b` on occurrence labels, Theorem 3.4). `m∗ ≥ 1` (every crossing set has a vertex, and
the case `m∗ = 0` follows from `m∗ = 1`). -/
theorem lemma_3_3 {α β : Type*} [DecidableEq α] [DecidableEq β] (B S C : Finset β)
    (X : β → Finset α) (ω : β → ℝ) (hω : ∀ b ∈ B, 0 ≤ ω b) (hS : S ⊆ B) (hC : C ⊆ B)
    (mstar : ℕ) (hm : 1 ≤ mstar)
    (hcross : ∀ F ⊆ B, IsConnSet X F → (F ∩ S).Nonempty → (F ∩ C).Nonempty → mstar ≤ F.card)
    (hdw : 6 * dwt B X ω < 1) :
    crossActivity B S C X ω ≤ zeta B S X ω mstar := by sorry

end LindbladShallow
