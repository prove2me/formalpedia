-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_theorem_D_8
-- name    : MatchIndiff.PublicSM.theorem_D_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:26:44.127823+00:00
-- url     : https://prove2.me/theorems/658855dd-faf7-460a-9105-646a113b6d4b
-- title:
--   Theorem D.8 — IJVC ≤ EJVC ≤ 5m_Q + 3n b_n + 2 (super: n b_n), hence O(n²)
-- statement:
--   Consider public-priority school choice with $n$ students and $n$ schools, an arbitrary public priority profile $Q$ (ties and unacceptable students allowed), arbitrary public orders, and the unrestricted student report domain. Let $m_Q$ be the number of pairs $(d,h)$ with $d$ acceptable to $h$ and $b_n=\lceil\log_2(n+1)\rceil$. For $\alpha\in\{s,u\}$ the canonical selector satisfies
--   $$\mathrm{IJVC}_Q(\Phi_\alpha)\le\mathrm{EJVC}_Q(\Phi_\alpha)\le 5m_Q+3nb_n+2,$$
--   and for super stability the term $3nb_n$ can be replaced by $nb_n$. The protocols include failure (the outputs are $\dagger$ when no $\alpha$-stable matching exists) and use only student-local checkers. Consequently both general joint-verification complexities are $O(n^2)$: there are $C,N$ with $\mathrm{JVC}^b_\xi(\Phi_\alpha)\le Cn^2$ for all $n\ge N$, all public inputs $\xi$, both selectors and both output types.
--
--   This is the upper half of the $\Theta(n^2)$ clause of Theorem 6.2.
--
--   Differences from the source:
--   - reading: for every public priority profile Q, JVC_Q (Q fixed, sup over the other public data) → for every valid public input ξ = (Q, ρ, τ) with n students and n schools; reason: a bound for every ξ is the bound on the supremum over ρ, τ; the bit count encodes schools and ⊥ in b_n bits, which presumes the balanced convention m = n of §6
--   - reading: IJVC_Q ≤ EJVC_Q → every exact protocol cost bound K yields a rank protocol of cost at most K; reason: JVC is a minimum over protocols; this is the inequality at the protocol level
--   - reading: both general joint-verification complexities are O(n²) → ∃ C N, ∀ n ≥ N, ∀ valid ξ, ∀ α ∈ {s, u}, ∀ b ∈ {I, E}, JVC ≤ C n²; reason: explicit content of O(·)
--   - encoding: board cost ⌈log₂|C|⌉, rank and exact outputs with † → JVCle with board alphabet Fin c and cost Nat.clog 2 c; Out n b with none = †; reason: Lean convention
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 99, Theorem D.8

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Protocol

namespace MatchIndiff.PublicSM

/-- Theorem D.8 (p. 99): for every public input with `n` students and `n` schools (public
priorities with arbitrary ties and unacceptable students), `IJVC ≤ EJVC ≤ 5 m_Q + 3 n b_n + 2`
for the strong selector and `≤ 5 m_Q + n b_n + 2` for the super selector, with
`b_n = ⌈log₂(n + 1)⌉`, on the unrestricted domain with failure included and student-local checks;
consequently both joint-verification complexities are `O(n²)`. -/
theorem theorem_D_8 :
    (∀ (n : ℕ) (ξ : PublicInput n n), ξ.Valid →
      (∀ α : StabKind, α ≠ StabKind.weak → ∀ K : ℕ,
        JVCle ξ α OutKind.exact (fullDomain n n) K → JVCle ξ α OutKind.rank (fullDomain n n) K) ∧
      JVCle ξ StabKind.strong OutKind.exact (fullDomain n n)
        (5 * mQ ξ.Q + 3 * n * Nat.clog 2 (n + 1) + 2) ∧
      JVCle ξ StabKind.super OutKind.exact (fullDomain n n)
        (5 * mQ ξ.Q + n * Nat.clog 2 (n + 1) + 2)) ∧
    (∃ C N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ξ : PublicInput n n, ξ.Valid →
      ∀ α : StabKind, α ≠ StabKind.weak → ∀ b : OutKind,
        JVCle ξ α b (fullDomain n n) (C * n ^ 2)) := by sorry

end MatchIndiff.PublicSM
