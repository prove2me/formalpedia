-- Prove2me | Theorems.Thm_MonoApport_Flow_lemma_5
-- name    : MonoApport.Flow.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:52.463777+00:00
-- url     : https://prove2.me/theorems/18c99f55-3df1-4b62-9aa6-b628d290a218
-- title:
--   Lemma 5, p. 42 — an extreme point with Φ(p, H) seats gives seat T + 1 (T ≤ H − 1) only to a state of ℒ ∩ 𝒰 at A(x, T)
-- statement:
--   Let $p\in\mathbb N^n$ be a vector of positive populations, $H\ge1$ a house size, and $\Phi(p,H)$ the lookahead of §5 (p. 20). Let $\mathcal E(p,\Phi(p,H))$ be the set of extreme points of the linear program (1)–(4) with $\Phi(p,H)$ seats, $A_i(x,T)=\sum_{\ell=1}^T x(i,\ell)$, and $\mathcal L$, $\mathcal U$ the Balinski–Young sets of §C.4.
--
--   **Lemma 5.** Let $x\in\mathcal E(p,\Phi(p,H))$. Then, for every $T\le H-1$,
--   $$x(i,T+1)=0\qquad\text{for every } i\notin\mathcal L(p,T,A(x,T))\cap\mathcal U(p,T,A(x,T)).$$
--
--   The lemma says that the seat sequence of an extreme point with $\Phi(p,H)$ seats follows the Balinski–Young construction for its first $H$ seats; with the characterization of Balinski and Young it gives the inclusion $\supseteq$ of Theorem 3.
--
--   **Formalization Note.** Seat $T+1$ is column `T` of `x : Fin n → Fin (Phi p H) → ℝ`; "$T\le H-1$" is `T + 1 ≤ H`, and $T=0$ is included as printed. Since $\Phi(p,H)\ge H$, the column exists for every such $T$.
--
--   Differences from the source:
--   - encoding: variables x(i, t) for seats t ∈ [L] = {1, …, L}, with prefix sums over ℓ = 1, …, t bounded by ⌊t pᵢ/P⌋ and ⌈t pᵢ/P⌉ → x : Fin n → Fin L → ℝ, column t : Fin L standing for seat t + 1; the bounds at column t are ⌊(t + 1) pᵢ/P⌋ and ⌈(t + 1) pᵢ/P⌉ on the sum over columns ℓ ≤ t; reason: 0-indexed relabelling of the seats; no instance changes
--   - encoding: k⋆ is a minimum over integers k ≥ 1, Φ(p, 1) a minimum and Φ(p, H + 1) a maximum → kStar and Phi p 1 use sInf on ℕ, Phi p (H + 2) uses sSup on ℕ; reason: the sets are nonempty (and the maximized set finite) at every argument where the paper uses them, so sInf and sSup are the paper's min and max; the junk value 0 of an empty set is never reached
-- source:
--   Cembrano, Correa, Schmidt-Kraepelin, Tsigonias-Dimitriadis & Verdugo, New Combinatorial Insights for Monotone Apportionment, arXiv:2410.23869v1, Lemma 5, p. 42 (proof pp. 42–43)

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

namespace MonoApport.Flow

/-- Lemma 5 (p. 42): for `x ∈ ℰ(p, Φ(p, H))` and every `T ≤ H − 1`, `x(i, T + 1) = 0` for every
`i ∉ ℒ(p, T, A(x, T)) ∩ 𝒰(p, T, A(x, T))`. Column `T` is seat `T + 1`. -/
theorem lemma_5 {n : ℕ} (p : Fin n → ℕ) (hp : IsPop p) (H : ℕ) (hH : 0 < H)
    (x : Fin n → Fin (Phi p H) → ℝ) (hx : x ∈ calE p (Phi p H)) :
    ∀ T : ℕ, T + 1 ≤ H → ∀ i : Fin n, i ∉ calL p T (A x T) ∩ calU p T (A x T) →
      ∀ t : Fin (Phi p H), t.val = T → x i t = 0 := by sorry

end MonoApport.Flow
