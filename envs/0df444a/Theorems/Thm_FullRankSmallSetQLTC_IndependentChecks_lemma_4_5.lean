-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_lemma_4_5
-- name    : FullRankSmallSetQLTC.IndependentChecks.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:01.443651+00:00
-- url     : https://prove2.me/theorems/29b65df7-3c77-4325-af2f-911e794067a5
-- title:
--   Lemma 4.5 — products of reduced shells are bijective in every ordering
-- statement:
--   Let $\ell\ge1$, let $p_1,\dots,p_\ell$ be distinct primes with $p_i\equiv1\pmod8$, and let $m\ge3$ satisfy (4.5): $2^m>2\sqrt{p_1\cdots p_\ell}$. For $I\subseteq[\ell]$ put $n_I=\prod_{i\in I}p_i$ and $A^{(m)}_I=\prod_{i\in I}A^{(m)}_{p_i}$. For every nonempty $I$ and every ordering of $I$, multiplication followed by reduction is a bijection
--   $$\prod_{i\in I}A(p_i)\xrightarrow{\ \sim\ }A^{(m)}_I=\pi_m\big(A(n_I)\big).$$
--   In particular $A^{(m)}_I$ does not depend on the ordering, and $|A^{(m)}_I|=\prod_{i\in I}(p_i+1)$.
--
--   Differences from the source:
--   - encoding: every ordering of I → a duplicate-free list l with underlying set I; the product set A_I^(m) is taken in the order of l; reason: an ordering of a finite set is such a list; equality with π_m(A(n_I)) for every list is the independence of the ordering
--   - encoding: A(n) = {a ∈ L(ℤ) : N(a) = n, a₀ odd}/{±1} → the set APos n of representatives with positive real part; a product of classes is written sgnNorm of the product of representatives; reason: the real part of each element is odd, hence nonzero, so each class has exactly one representative with a₀ > 0; same instances
--   - encoding: π_m : 1 + 2L(ℤ₂) → Ĝ_m (reduction mod 2^m, then the quotient by scalars), Ĝ_m = U_m/R_m^×, G_m the norm ≡ 1 (mod 8) classes → pim m on integral quaternions (value 1 off the domain a ≡ 1 mod 2); U_m the units of L(ℤ/2^m) reducing to 1 mod 2; G_m the image of the units with norm ≡ 1 (mod 2^min(m,3)); reason: every quaternion the source reduces in this statement is integral and ≡ 1 (mod 2); for m ≥ 3 the groups are those of Definition 4.1
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Lemma 4.5, p. 22 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Quaternion Pointwise

/-- **Lemma 4.5** (p. 22). Let `ℓ ≥ 1`, let `p₁, …, p_ℓ` be distinct primes `≡ 1 (mod 8)` and let
`m ≥ 3` satisfy (4.5): `2^m > 2√(p₁ ⋯ p_ℓ)`. For every nonempty `I ⊆ [ℓ]` and every ordering of
`I` (a duplicate-free list `l` with underlying set `I`), multiplication followed by reduction is a
bijection `∏_{i ∈ I} A(p_i) → π_m(A(n_I))`, `n_I = ∏_{i∈I} p_i`; the product set
`A_I^{(m)} = ∏_{i∈I} A_{p_i}^{(m)}` taken in that ordering equals `π_m(A(n_I))` (so it does not
depend on the ordering), and `|A_I^{(m)}| = ∏_{i∈I} (p_i + 1)`. -/
theorem lemma_4_5 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ps : Fin ℓ → ℕ) (hinj : Function.Injective ps)
    (hp : ∀ i, (ps i).Prime ∧ ps i % 8 = 1) (m : ℕ) (hm : 3 ≤ m)
    (hsep : 2 * Real.sqrt ((∏ i, ps i : ℕ) : ℝ) < 2 ^ m)
    (I : Finset (Fin ℓ)) (hI : I.Nonempty) (l : List (Fin ℓ)) (hl : l.Nodup)
    (hlI : l.toFinset = I) :
    Set.BijOn (fun f : Fin l.length → ℍ[ℤ] => pim m (List.ofFn f).prod)
      (Set.univ.pi fun j => APos (ps (l.get j))) (Ared m (∏ i ∈ I, ps i)) ∧
    (l.map fun i => Ared m (ps i)).prod = Ared m (∏ i ∈ I, ps i) ∧
    (Ared m (∏ i ∈ I, ps i)).ncard = ∏ i ∈ I, (ps i + 1) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
