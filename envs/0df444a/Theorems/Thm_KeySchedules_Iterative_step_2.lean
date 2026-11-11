-- Prove2me | Theorems.Thm_KeySchedules_Iterative_step_2
-- name    : KeySchedules.Iterative.step_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:51:05.482776+00:00
-- url     : https://prove2.me/theorems/5f92c04b-86bf-4f72-848c-d1b812ae678f
-- title:
--   Proof of Lemma 3.2, Step 2 — image exchanges condition a uniform permutation on a state path and move X by at most 2r²/|S|
-- statement:
--   Let $\mathrm{Out}$ be balanced, $h:G^r\to[0,1]$, $s\in S$ and $z\in S^r$ with $\Pr_\varphi[E_{s,z}]>0$, where $E_{s,z}=\{\mathrm{Path}_\varphi(s)=z\}$. Then:
--
--   1. $E_{s,z}$ is the conjunction of the constraints $\varphi(a_j)=b_j$ ($1\le j\le\ell$) left after removing repetitions; $\ell\le r$, the $a_j$ are distinct and the $b_j$ are distinct.
--   2. The image-exchange procedure always yields a permutation in $E_{s,z}$, and applied to a uniform permutation it yields a uniform permutation conditioned on $E_{s,z}$: each $\psi\in E_{s,z}$ arises with probability $1/|E_{s,z}|$.
--   3. Its output differs from its input by at most $\ell\le r$ image exchanges.
--   4. One image exchange $\varphi\mapsto\varphi\circ(a\ x)$ changes $X$ by at most $2r/|S|$, and the procedure changes $X$ by at most
--   $$|X(\varphi')-X(\varphi)|\le\frac{2r^2}{|S|}.$$
--
--   This coupling is what replaces independence in the exponential-moment argument of Step 3.
--
--   Differences from the source:
--
--   - encoding: the procedure applied to a uniform permutation gives a uniform permutation conditioned on E_{s,z} → its output always lies in E_{s,z}, and for every ψ ∈ E_{s,z} the fraction of permutations mapped to ψ is 1/|E_{s,z}|; reason: the push-forward of the uniform distribution equals the uniform distribution on E_{s,z}
--   - reading: constraints enforced 'one at a time', with repeated constraints removed → the list (a_i, z_i), i = 1, …, r, with List.dedup, enforced by a left fold in list order; reason: the paper fixes no order; the clauses hold for this one
--   - encoding: differs from the initial permutation by at most ℓ ≤ r image exchanges → exchange φ = φ * (product of a list of at most ℓ transpositions), together with ℓ ≤ r; reason: an image exchange φ ↦ φ ∘ (a x) is right multiplication by a transposition
--   - generalization: one exchange of the procedure changes X by at most 2r/|S| → every exchange φ ↦ φ ∘ (a x), for every φ, a, x, changes X by at most 2r/|S|; reason: the paper's argument does not use which exchange it is; the procedure's exchanges are among these
--   - encoding: Pr_φ / E_φ for a uniform permutation φ of S → counts and averages over the finite type Equiv.Perm S; reason: uniform probability on a finite set is a counting ratio; same statement
--   - encoding: |G| ∣ |S| and |Out⁻¹(k)| = |S|/|G| for every k → IsBalanced Out: |Out⁻¹(k)| · |G| = |S| for every k; reason: equivalent; the product form implies the divisibility, so it is not a separate hypothesis
--   - encoding: h : G^r → [0, 1] → h : (Fin r → G) → ℝ with 0 ≤ h ≤ 1 as hypotheses; reason: same functions
--   - encoding: rounds and coordinates 1, …, r → Fin r, index i standing for round i + 1; reason: index base only
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 12, proof of Lemma 3.2, Step 2

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Schedule

namespace KeySchedules.Iterative

/-- Proof of Lemma 3.2, Step 2 (p. 12): for a master key `s` and a state path `z` with
`Pr_φ[E_{s,z}] > 0`, where `E_{s,z} = {Path_φ(s) = z}`:
* the event is the conjunction of the constraints `φ(a_j) = b_j` listed by `constraints s z`
  (repetitions removed), there are `ℓ ≤ r` of them, the `a_j` are distinct and the `b_j` are
  distinct;
* the image-exchange procedure always produces a permutation in `E_{s,z}`, and applied to a
  uniform permutation it produces a uniform permutation conditioned on `E_{s,z}`: every `ψ`
  in `E_{s,z}` is produced with probability `1/|E_{s,z}|`;
* its output differs from its input by at most `ℓ` image exchanges;
* one image exchange `φ ↦ φ ∘ (a x)` changes `X` by at most `2r/|S|`, and the procedure
  changes `X` by at most `2r²/|S|` (for `h : G^r → [0, 1]`). -/
theorem step_2 {S G : Type} [AddCommGroup G] [Fintype G] [Fintype S] [DecidableEq S]
    [Nonempty S] (r : ℕ) (hr : 1 ≤ r) (Out : S → G) (hOut : IsBalanced Out)
    (h : (Fin r → G) → ℝ) (h0 : ∀ k, 0 ≤ h k) (h1 : ∀ k, h k ≤ 1)
    (s : S) (z : Fin r → S) (hpos : ∃ φ : Equiv.Perm S, statePath φ r s = z) :
    (∀ φ : Equiv.Perm S, statePath φ r s = z ↔ ∀ c ∈ constraints s z, φ c.1 = c.2) ∧
    (constraints s z).length ≤ r ∧
    ((constraints s z).map Prod.fst).Nodup ∧
    ((constraints s z).map Prod.snd).Nodup ∧
    (∀ φ : Equiv.Perm S, statePath (exchange s z φ) r s = z) ∧
    (∀ ψ : Equiv.Perm S, statePath ψ r s = z →
      ({φ : Equiv.Perm S | exchange s z φ = ψ}.ncard : ℝ) / (Fintype.card (Equiv.Perm S) : ℝ)
        = 1 / ({φ : Equiv.Perm S | statePath φ r s = z}.ncard : ℝ)) ∧
    (∀ φ : Equiv.Perm S, ∃ l : List (S × S), l.length ≤ (constraints s z).length ∧
      exchange s z φ = φ * (l.map (fun c => Equiv.swap c.1 c.2)).prod) ∧
    (∀ (φ : Equiv.Perm S) (a x : S),
      |avgX Out h (φ * Equiv.swap a x) - avgX Out h φ| ≤ 2 * (r : ℝ) / (Fintype.card S : ℝ)) ∧
    (∀ φ : Equiv.Perm S,
      |avgX Out h (exchange s z φ) - avgX Out h φ|
        ≤ 2 * (r : ℝ) ^ 2 / (Fintype.card S : ℝ)) := by sorry

end KeySchedules.Iterative
