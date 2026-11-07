-- Prove2me | Theorems.Thm_MeanBudgetXC_section_4_3_host
-- name    : MeanBudgetXC.section_4_3_host
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:52.480407+00:00
-- url     : https://prove2.me/theorems/80866f98-9420-4756-a256-f59c5ce5d498
-- title:
--   Section 4.3 — the host graph: size, triangle-freeness, degree and edge counts
-- statement:
--   Let $Q$ be the host graph built from $n_0$ source variables per side, $\ell$ copies of a padding graph $T$ of order $t$, $c$ marker edges and $n_{\mathrm{iso}}$ isolates.
--
--   1. $Q$ has $8n_0+t\ell+2c+n_{\mathrm{iso}}$ vertices, which is $N$ by (15).
--   2. $Q$ is triangle-free when $T$ is.
--   3. If $n_0\ge1$ and $\ell\ge1$, then $\Delta(Q)=\max\{2n_0+1,\Delta(T),2\}$.
--   4. The heavy edges (path, padding and marker edges) number $m_{\mathrm{heavy}}=6n_0+\ell|E(T)|+c$.
--   5. $|E|=4n_0^2+m_{\mathrm{heavy}}$.
--   6. Every canonical choice has size $4n_0+v\ell+c$, which is $d$ by (15), where $v$ is the minimum vertex-cover size of $T$.
--
--   These are the size and degree facts the zero-face construction needs.
--
--   **Formalization Note** Heavy edges are recognized as the edges not joining two path endpoints.
--
--   Differences from the source:
--   - generalization: the host at the parameters (15) of Section 4.2 → the host at arbitrary $n_0,t,\ell,c,n_{\mathrm{iso}}$ and $T$ (with $n_0,\ell\ge1$ in the degree clause only); reason: the counts do not use (15); at those parameters and large $N$, $n_0,\ell\ge1$ hold, so the paper's statement is a special case
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.3, p.19; $|E|$ on p.21

import Mathlib
import Definitions.Def_MeanBudgetXC_hostGraph
import Definitions.Def_MeanBudgetXC_isEndpoint
import Definitions.Def_MeanBudgetXC_heavyCount
import Definitions.Def_MeanBudgetXC_IsCanonical

namespace MeanBudgetXC

/-- **Section 4.3, the host graph and its counts** (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget
Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76,
Section 4.3, p.19; `|E|` on p.21). For the host `Q` built from `n₀` source variables per side,
`ℓ` copies of the padding graph `T` of order `t`, `c` marker edges and `n_iso` isolates:
1. `Q` has `8n₀ + tℓ + 2c + n_iso` vertices (which is `N` by (15));
2. `Q` is triangle-free when `T` is;
3. `Δ(Q) = max{2n₀ + 1, Δ(T), 2}`;
4. the heavy edges (path, padding and marker edges) number `m_heavy = 6n₀ + ℓ|E(T)| + c`;
5. `|E| = 4n₀² + m_heavy`;
6. every canonical choice has size `4n₀ + vℓ + c` (which is `d` by (15)), `v` the minimum
   vertex-cover size of `T`.

**Formalization Note** The heavy edges are the edges not joining two path endpoints (the
interaction edges are exactly the edges between path endpoints). Clause 3 assumes `n₀ ≥ 1` and
`ℓ ≥ 1`, as in the paper's parameter range (`n₀ = Ω_θ(N)`, and `ℓ ≥ 1` for large `N`): without a
padding copy `Δ(T)` does not occur in `Q`. -/
theorem section_4_3_host (n₀ t ℓ c niso : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] :
    Fintype.card (HostV n₀ t ℓ c niso) = 8 * n₀ + t * ℓ + 2 * c + niso ∧
      (T.CliqueFree 3 → (hostGraph n₀ t ℓ c niso T).CliqueFree 3) ∧
      (1 ≤ n₀ → 1 ≤ ℓ →
        (hostGraph n₀ t ℓ c niso T).maxDegree = max (max (2 * n₀ + 1) T.maxDegree) 2) ∧
      ((hostGraph n₀ t ℓ c niso T).edgeFinset.filter
          (fun e => ¬ ∀ x ∈ e.toFinset, isEndpoint x = true)).card = heavyCount n₀ ℓ c T ∧
      (hostGraph n₀ t ℓ c niso T).edgeFinset.card = 4 * n₀ ^ 2 + heavyCount n₀ ℓ c T ∧
      ∀ S : Finset (HostV n₀ t ℓ c niso), IsCanonical T S →
        S.card = 4 * n₀ + T.vertexCoverNum.toNat * ℓ + c := by sorry

end MeanBudgetXC
