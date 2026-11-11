-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_theorem_4_2
-- name    : FullRankSmallSetQLTC.IndependentChecks.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:54.808334+00:00
-- url     : https://prove2.me/theorems/8b7073b9-3370-4221-8928-db4718090dd2
-- title:
--   Theorem 4.2 — LPS Ramanujan graphs on 2-groups
-- statement:
--   Let $p\equiv1\pmod4$ be prime and let $m\ge3$ satisfy $2^m>2\sqrt p$. Then $A^{(m)}_p=\pi_m(A(p))$ consists of $p+1$ distinct nonidentity elements, and $\mathrm{Cay}(\langle A^{(m)}_p\rangle;A^{(m)}_p)$ is a simple, connected, $(p+1)$-regular Ramanujan graph: every adjacency eigenvalue $\lambda\neq\pm(p+1)$ satisfies $|\lambda|\le2\sqrt p$. Moreover:
--
--   1. if $p\equiv1\pmod8$, then $\langle A^{(m)}_p\rangle=G_m$, the graph is non-bipartite, and its girth is at least $\tfrac23\log_p|G_m|$;
--   2. if $p\equiv5\pmod8$, then $\langle A^{(m)}_p\rangle=\widehat G_m$, the graph is bipartite with parts $G_m$ and $\widehat G_m\setminus G_m$, and its girth is at least $\tfrac43\log_p|\widehat G_m|$.
--
--   This is the 2-adic analogue of the LPS theorem, with $G_m\subseteq\widehat G_m$ in the role of $\mathrm{PSL}_2(\mathbb F_q)\subseteq\mathrm{PGL}_2(\mathbb F_q)$.
--
--   Differences from the source:
--   - encoding: A_p^(m) consists of p+1 distinct nonidentity elements and Cay(⟨A⟩; A) is a simple (p+1)-regular graph → π_m is injective on A(p), |π_m(A(p))| = p+1, 1 ∉ π_m(A(p)), π_m(A(p)) is closed under inverses, and the SimpleGraph with g ∼ k iff g ≠ k and g⁻¹k or k⁻¹g lies in the set is connected, (p+1)-regular and Ramanujan; reason: a Cayley graph with edges g — ga is a simple undirected (p+1)-regular graph exactly when the p+1 generators are distinct, nonidentity and inverse-closed; the extra clauses restate what simplicity and regularity mean
--   - encoding: non-bipartite; bipartite with parts G_m and Ĝ_m∖G_m; girth at least b → not 2-colorable; every edge joins G_m to its complement; every cycle has length ≥ b; reason: standard graph-theoretic definitions
--   - encoding: A(n) = {a ∈ L(ℤ) : N(a) = n, a₀ odd}/{±1} → the set APos n of representatives with positive real part; a product of classes is written sgnNorm of the product of representatives; reason: the real part of each element is odd, hence nonzero, so each class has exactly one representative with a₀ > 0; same instances
--   - encoding: π_m : 1 + 2L(ℤ₂) → Ĝ_m (reduction mod 2^m, then the quotient by scalars), Ĝ_m = U_m/R_m^×, G_m the norm ≡ 1 (mod 8) classes → pim m on integral quaternions (value 1 off the domain a ≡ 1 mod 2); U_m the units of L(ℤ/2^m) reducing to 1 mod 2; G_m the image of the units with norm ≡ 1 (mod 2^min(m,3)); reason: every quaternion the source reduces in this statement is integral and ≡ 1 (mod 2); for m ≥ 3 the groups are those of Definition 4.1
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Theorem 4.2, p. 19 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Quaternion Pointwise

open Classical in
/-- **Theorem 4.2** (LPS Ramanujan graphs on 2-groups, p. 19). Let `p ≡ 1 (mod 4)` be prime and
`m ≥ 3` with `2^m > 2√p`. Then `A_p^{(m)} = π_m(A(p))` consists of `p + 1` distinct nonidentity
elements (closed under inverses), and `Cay(⟨A_p^{(m)}⟩; A_p^{(m)})` is a simple connected
`(p+1)`-regular Ramanujan graph. Moreover:
1. if `p ≡ 1 (mod 8)`, then `⟨A_p^{(m)}⟩ = G_m`, the graph is non-bipartite and its girth is at
   least `(2/3) log_p |G_m|`;
2. if `p ≡ 5 (mod 8)`, then `⟨A_p^{(m)}⟩ = Ĝ_m`, the graph is bipartite with parts `G_m` and
   `Ĝ_m ∖ G_m`, and its girth is at least `(4/3) log_p |Ĝ_m|`. -/
theorem theorem_4_2 (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (m : ℕ) (hm : 3 ≤ m)
    (hsep : 2 * Real.sqrt p < 2 ^ m) :
    Set.InjOn (pim m) (APos p) ∧ (Ared m p).ncard = p + 1 ∧ (1 : GHat m) ∉ Ared m p ∧
    (∀ g ∈ Ared m p, g⁻¹ ∈ Ared m p) ∧
    IsRamanujan (cayleyGraph (Subgroup.closure (Ared m p)) (Ared m p)) (p + 1) ∧
    (p % 8 = 1 →
      Subgroup.closure (Ared m p) = Gm m ∧
      ¬ (cayleyGraph (Subgroup.closure (Ared m p)) (Ared m p)).Colorable 2 ∧
      GirthAtLeast (cayleyGraph (Subgroup.closure (Ared m p)) (Ared m p))
        ((2 / 3) * Real.logb p (Nat.card (Gm m)))) ∧
    (p % 8 = 5 →
      Subgroup.closure (Ared m p) = ⊤ ∧
      (∀ g g' : ↥(Subgroup.closure (Ared m p)),
        (cayleyGraph (Subgroup.closure (Ared m p)) (Ared m p)).Adj g g' →
          ((g : GHat m) ∈ Gm m ↔ (g' : GHat m) ∉ Gm m)) ∧
      GirthAtLeast (cayleyGraph (Subgroup.closure (Ared m p)) (Ared m p))
        ((4 / 3) * Real.logb p (Nat.card (GHat m)))) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
