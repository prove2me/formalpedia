-- Prove2me | Theorems.Thm_ImplicitParityWL_theorem_1_3_colored
-- name    : ImplicitParityWL.theorem_1_3_colored
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:08.532678+00:00
-- url     : https://prove2.me/theorems/265f8546-a7de-41cc-8c5d-c1933fbc3029
-- title:
--   §6, proof of Theorem 1.3 — the compiled counter pairs: order $\Theta_k(2^\ell)$, first round $\Theta_k(\tau_\ell)$
-- statement:
--   Let $k\ge3$. There are constants $C_k,b_k>0$ such that for every $\ell\ge1$, the colored graphs $G_0^{(\ell)},G_1^{(\ell)}$ compiled from the counter $\mathcal I^{k,\ell}_{\mathrm{ctr}}$ have the same number $n_\ell$ of vertices, with
--   $$
--   2k\cdot2^\ell\le n_\ell\le C_k2^\ell,
--   $$
--   and $k$-WL first distinguishes them after $T_\ell$ rounds, with
--   $$
--   \tau_\ell-k\le T_\ell\le b_k(\tau_\ell+1),\qquad \tau_\ell=3\cdot2^{(k-1)\ell-1}.
--   $$
--   Consequently $T_\ell=\Theta_k(n_\ell^{k-1})$, which is the content of the proof of Theorem 1.3 for colored graphs.
--
--   **Formalization Note** The first inequality is written $\tau_\ell\le T_\ell+k$, without truncated subtraction. $C_k$ and $b_k$ are natural numbers chosen before $\ell$.
--
--   Differences from the source:
--   - encoding: τ_ℓ − k ≤ T_ℓ → τ_ℓ ≤ T_ℓ + k; reason: the same inequality without truncated subtraction
--   - encoding: constants C_k, b_k > 0 → natural numbers C_k, b_k > 0; reason: a natural constant loses nothing against a real one
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §6, proof of Theorem 1.3, pp.35–36

import Mathlib
import Definitions.Def_ImplicitParityWL_WLColor
import Definitions.Def_ImplicitParityWL_CompiledGraph
import Definitions.Def_ImplicitParityWL_Counter

namespace ImplicitParityWL

/-- The colored statement proved in **§6, proof of Theorem 1.3** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, pp.35–36): for `k ≥ 3` there are constants `C_k`, `b_k`
such that for every `ℓ ≥ 1`, the colored graphs `G₀^{(ℓ)}`, `G₁^{(ℓ)}` compiled from `ℐ_ctr^{k,ℓ}` have the same number `n_ℓ` of
vertices with `2k · 2^ℓ ≤ n_ℓ ≤ C_k 2^ℓ`, and they are first distinguished by `k`-WL after `T_ℓ` rounds with
`τ_ℓ - k ≤ T_ℓ ≤ b_k (τ_ℓ + 1)`, where `τ_ℓ = 3 · 2^{(k-1)ℓ-1}`.

**Formalization Note** The lower bound is written `τ_ℓ ≤ T_ℓ + k`, without truncated subtraction. The constants are chosen
before `ℓ`. -/
theorem theorem_1_3_colored (k : ℕ) (hk : 3 ≤ k) : ∃ Ck b : ℕ, 0 < Ck ∧ 0 < b ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
    Fintype.card ((counter k ℓ).Vertex 0) = Fintype.card ((counter k ℓ).Vertex 1) ∧
    2 * k * 2 ^ ℓ ≤ Fintype.card ((counter k ℓ).Vertex 0) ∧
    Fintype.card ((counter k ℓ).Vertex 0) ≤ Ck * 2 ^ ℓ ∧
    ∃ T : ℕ, FirstDistinguishedAt ((counter k ℓ).graph 0) ((counter k ℓ).graph 1) k T ∧
      3 * 2 ^ ((k - 1) * ℓ - 1) ≤ T + k ∧
      T ≤ b * (3 * 2 ^ ((k - 1) * ℓ - 1) + 1) := by sorry

end ImplicitParityWL
