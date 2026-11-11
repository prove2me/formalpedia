-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_theorem_4_6
-- name    : FullRankSmallSetQLTC.IndependentChecks.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:38.279884+00:00
-- url     : https://prove2.me/theorems/15cf3633-679f-4c56-bc2d-4617c82f2189
-- title:
--   Theorem 4.6 — Ramanujan cubical complexes on 2-groups
-- statement:
--   Let $\ell\ge1$, let $p_1,\dots,p_\ell$ be distinct primes with $p_i\equiv1\pmod8$, and let $m\ge3$ satisfy (4.5): $2^m>2\sqrt{p_1\cdots p_\ell}$. Then the sets $A^{(m)}_{p_1},\dots,A^{(m)}_{p_\ell}$ lie in $G_m$, are cubical generating sets of $G_m$ with $|A^{(m)}_{p_i}|=p_i+1$, and the decorated cubical complex
--   $$Y_m=\mathrm{Cay}(G_m;A^{(m)}_{p_1},\dots,A^{(m)}_{p_\ell})$$
--   is $2^\ell$-expanding: for every nonempty $I\subseteq[\ell]$ the operator $T_I$ has norm at most $2^\ell\sqrt{d_I}$ on the functions orthogonal to the constants.
--
--   These complexes replace the HLMRZ complexes over $\mathrm{PSL}_2(\mathbb F_q)$ by complexes over a fixed family of 2-groups.
--
--   Differences from the source:
--   - encoding: the complex is 2^ℓ-expanding: second largest eigenvalue of each mixed-direction graph at most 2^ℓ√d_I → ‖T_I f‖₂ ≤ 2^ℓ √d_I ‖f‖₂ for every complex-valued f on G_m with Σ f = 0 and every nonempty I; reason: the source states that the two formulations are equivalent (p. 22); ℓ²(G) over ℂ
--   - encoding: A_{p_i}^(m) as subsets of G_m → the conclusion π_m(A(p_i)) ⊆ G_m together with the preimages of these sets in the subtype G_m; reason: Lean distinguishes a subset of Ĝ_m from a subset of the group G_m; the containment is asserted
--   - encoding: A(n) = {a ∈ L(ℤ) : N(a) = n, a₀ odd}/{±1} → the set APos n of representatives with positive real part; a product of classes is written sgnNorm of the product of representatives; reason: the real part of each element is odd, hence nonzero, so each class has exactly one representative with a₀ > 0; same instances
--   - encoding: π_m : 1 + 2L(ℤ₂) → Ĝ_m (reduction mod 2^m, then the quotient by scalars), Ĝ_m = U_m/R_m^×, G_m the norm ≡ 1 (mod 8) classes → pim m on integral quaternions (value 1 off the domain a ≡ 1 mod 2); U_m the units of L(ℤ/2^m) reducing to 1 mod 2; G_m the image of the units with norm ≡ 1 (mod 2^min(m,3)); reason: every quaternion the source reduces in this statement is integral and ≡ 1 (mod 2); for m ≥ 3 the groups are those of Definition 4.1
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Theorem 4.6, p. 23 (setting and (4.5) on p. 22) (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Cubical

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Quaternion Pointwise

open Classical in
/-- **Theorem 4.6** (Ramanujan cubical complexes on 2-groups, p. 23). Let `ℓ ≥ 1`, let
`p₁, …, p_ℓ` be distinct primes `≡ 1 (mod 8)` and let `m ≥ 3` satisfy (4.5):
`2^m > 2√(p₁ ⋯ p_ℓ)`. Then the sets `A_{p_i}^{(m)}` lie in `G_m`, are cubical generating sets of
`G_m` with `|A_{p_i}^{(m)}| = p_i + 1`, and the decorated cubical complex
`Y_m = Cay(G_m; A_{p₁}^{(m)}, …, A_{p_ℓ}^{(m)})` is `2^ℓ`-expanding. -/
theorem theorem_4_6 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ps : Fin ℓ → ℕ) (hinj : Function.Injective ps)
    (hp : ∀ i, (ps i).Prime ∧ ps i % 8 = 1) (m : ℕ) (hm : 3 ≤ m)
    (hsep : 2 * Real.sqrt ((∏ i, ps i : ℕ) : ℝ) < 2 ^ m) :
    (∀ i, Ared m (ps i) ⊆ (Gm m : Set (GHat m))) ∧
    IsCubicalGenSet (fun i => AredG m (ps i)) ∧
    (∀ i, (AredG m (ps i)).ncard = ps i + 1) ∧
    IsExpanding (fun i => AredG m (ps i)) (2 ^ ℓ) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
