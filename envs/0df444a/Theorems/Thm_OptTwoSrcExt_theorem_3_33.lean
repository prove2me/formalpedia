-- Prove2me | Theorems.Thm_OptTwoSrcExt_theorem_3_33
-- name    : OptTwoSrcExt.theorem_3_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:38.519373+00:00
-- url     : https://prove2.me/theorems/08814a4f-91eb-4b11-83eb-4b96b4f04854
-- title:
--   Theorem 3.33 — one-sided non-malleable sumset seed: $G_n(X+Y)$ with error $2^{-e_\sigma n}$, output $q_n\ge c_\sigma n$ and $O_\sigma(n)$ character rank
-- statement:
--   Fix $0<\sigma\le1$. There are constants $c_\sigma,e_\sigma>0$, a constant $A_\sigma$ and a deterministic polynomial-time map $G_n:\mathbb F_2^n\to\mathbb F_2^{q_n}$ with $q_n\ge c_\sigma n$, defined for every $n\ge1$, such that:
--
--   1. for independent sources $X,Y$ on $\mathbb F_2^n$ of min-entropy at least $\sigma n$ and every map $f$ with no fixed points on $\operatorname{supp}X$,
--   $$\big(G_n(X+Y),\,G_n(f(X)+Y)\big)\approx_{2^{-e_\sigma n}}\big(U_{q_n},\,G_n(f(X)+Y)\big),$$
--   with $U_{q_n}$ uniform and independent of the tampered output;
--   2. for the same sources, $\Delta(G_n(X+Y),U_{q_n})\le 2^{-e_\sigma n}$ (ordinary extraction);
--   3. every output character $(x,y)\mapsto\lambda\cdot G_n(x+y)$ has binary rank at most $A_\sigma n$ as a $2^n\times2^n$ table;
--   4. every one-comparison mixed character $(x,y)\mapsto\lambda\cdot G_n(x+y)+\mu\cdot G_n(f(x)+y)$, for every map $f$, has binary rank at most $A_\sigma n$.
--
--   Here $X+Y$ is coordinatewise addition over $\mathbb F_2$; only the first summand is tampered. This seed is the first stage of the extractor of Theorem 1.5: Construction 4.1 uses $S=\mathrm{prefix}_d\,G_n(x+y)$ at $\sigma=\delta/4$.
--
--   **Formalization Note** "Deterministic polynomial-time map" is one polynomial-time Turing machine $F$ with $G_n(z)=F[z]$ for all $n$, chosen after $\sigma$; $O_\sigma(n)$ is $A_\sigma n$ with $A_\sigma$ chosen before $n$; "global lifted binary rank" is the binary rank of the full table in $(x,y)$.
--
--   Differences from the source:
--   - reading: a deterministic polynomial-time map G_n for every positive n → one polynomial-time machine F with G_n(z) = F [z] for all n ≥ 1, chosen after σ; reason: explicit means computable by one polynomial-time algorithm (Definition 1.1, p.1), and the same seed architecture is shown uniformly explicit for Theorem 3.22 (p.46, PDF p.48, "This proves uniform explicitness"); a per-n map is computable trivially
--   - reading: every one-comparison mixed character has rank O_σ(n) → λ·G(x+y) + μ·G(f(x)+y) has rank ≤ A n for every map f and all λ, μ; reason: a table's rank does not involve the sources, and separate precomposition cannot increase rank (Lemma 3.27)
--   - reading: Ordinary extraction follows by choosing any nonzero translation f and projecting the honest output → a conjunct Δ(G(X+Y), U_q) ≤ 2^{−e n} for the same sources; reason: the printed consequence, at the same error
--   - encoding: O_σ(n); F_2^n → A·n with A chosen before n; Fin n → ZMod 2 written to the machine as a bit list; reason: Lean convention; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.33, p.48 (PDF p.50)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_rank2
import Definitions.Def_OptTwoSrcExt_fourier
import Definitions.Def_OptTwoSrcExt_machineVec

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt

/-- **Theorem 3.33 (One-sided non-malleable sumset seed).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.33, printed p.48 (PDF p.50): "For every fixed
0 < σ ⩽ 1, there are cσ, eσ > 0 and a deterministic polynomial-time map Gn : F_2^n → F_2^{qn},
qn ⩾ cσn, such that independent sources of min-entropy at least σn and every f with no fixed points
on supp X satisfy (Gn(X + Y), Gn(f(X) + Y)) ≈_{2^{−eσn}} (Uqn, Gn(f(X) + Y)). (3.36) Every output
character has global lifted binary rank Oσ(n), as does every one-comparison mixed character.
Ordinary extraction follows by choosing any nonzero translation f and projecting the honest output.
The family is defined for every positive integer n, using the finite-length completion specified
below."

For `0 < σ ≤ 1` there are `c, e > 0`, a rank constant `A` and one polynomial-time machine `F` such that
for every `n ≥ 1` there is `q ≥ cn` for which `G(z) = F [z]` maps `𝔽₂ⁿ` to exactly `q` bits and:
1. for independent `X, Y` on `𝔽₂ⁿ` with `H∞ ≥ σn` and every `f` with `f(x) ≠ x` on `supp X`,
   `Δ((G(X + Y), G(f(X) + Y)), (U_q, G(f(X) + Y))) ≤ 2^{−en}` (`U_q` independent of `G(f(X) + Y)`);
2. for the same sources, `Δ(G(X + Y), U_q) ≤ 2^{−en}` (ordinary extraction);
3. every output character `(x, y) ↦ λ·G(x + y)` has `rank₂ ≤ An`;
4. every one-comparison mixed character `(x, y) ↦ λ·G(x + y) + μ·G(f(x) + y)`, for every map `f`,
   has `rank₂ ≤ An`.

**Formalization Note.** `𝔽₂ⁿ` is `Fin n → ZMod 2`, written to the machine as a bit list
(`bitsOfVec`); `X + Y` is coordinatewise addition mod 2. "Deterministic polynomial-time map" is one
`LowErrExt.IsPolyTime` machine for all `n` (chosen after `σ`). "Global lifted binary rank" is
`rank2` of the full `2ⁿ × 2ⁿ` table in `(x, y)`; `O_σ(n)` is `An` with `A` chosen before `n`. The
mixed-character rank bound is stated for every map `f` (rank does not depend on the sources). Clause 2
is the printed consequence "ordinary extraction follows", stated as its own conjunct. -/
theorem theorem_3_33 (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ c e A : ℝ, 0 < c ∧ 0 < e ∧ ∃ F : List (List Bool) → List Bool, IsPolyTime F ∧
      ∀ n : ℕ, 1 ≤ n → ∃ q : ℕ, c * n ≤ q ∧
        (∀ z : Fin n → ZMod 2, (F [bitsOfVec z]).length = q) ∧
        (∀ X Y : PMF (Fin n → ZMod 2), σ * n ≤ minEntropy X → σ * n ≤ minEntropy Y →
          (∀ f : (Fin n → ZMod 2) → (Fin n → ZMod 2), (∀ x ∈ X.support, f x ≠ x) →
            statDist ((indepPair X Y).map fun r =>
                (machineVec F q [bitsOfVec (r.1 + r.2)], machineVec F q [bitsOfVec (f r.1 + r.2)]))
              (indepPair (PMF.uniformOfFintype (Fin q → ZMod 2))
                ((indepPair X Y).map fun r => machineVec F q [bitsOfVec (f r.1 + r.2)])) ≤
              (2 : ℝ) ^ (-(e * n))) ∧
          statDist ((indepPair X Y).map fun r => machineVec F q [bitsOfVec (r.1 + r.2)])
              (PMF.uniformOfFintype (Fin q → ZMod 2)) ≤ (2 : ℝ) ^ (-(e * n))) ∧
        (∀ l : Fin q → ZMod 2,
          (rank2 (fun x y : Fin n → ZMod 2 => dotF2 l (machineVec F q [bitsOfVec (x + y)])) : ℝ) ≤
            A * n) ∧
        (∀ (f : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (l μ : Fin q → ZMod 2),
          (rank2 (fun x y : Fin n → ZMod 2 =>
              dotF2 l (machineVec F q [bitsOfVec (x + y)]) +
                dotF2 μ (machineVec F q [bitsOfVec (f x + y)])) : ℝ) ≤ A * n) := by sorry

end OptTwoSrcExt
