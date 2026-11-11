-- Prove2me | Theorems.Thm_OptTwoSrcExt_theorem_3_17
-- name    : OptTwoSrcExt.theorem_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:39.349997+00:00
-- url     : https://prove2.me/theorems/06d08305-ccde-4339-aa03-b0358507f768
-- title:
--   Theorem 3.17 — constant-seed linear strong condenser above half (corrected: $n\ge n_0$)
-- statement:
--   Fix $\rho>0$ and $\varepsilon_*>0$. There are constants $\beta>0$, a power of two $Q\ge16$, constants $c_1,c_2>0$, a threshold $n_0$ and explicit $\mathbb F_2$-linear maps $L_u:\mathbb F_2^n\to\mathbb F_2^M$, indexed by seeds $u$ in a set of size $Q$, with $c_1n\le M\le c_2n$, such that for every $n\ge n_0$ and every source $X$ on $\mathbb F_2^n$ with $H_\infty(X)\ge\rho n$,
--   $$\frac1Q\sum_{u}\ \min_{Z_u:\,H_\infty(Z_u)\ge(1/2+\beta/2)M}\Delta(L_uX,Z_u)\le\varepsilon_* .\tag{3.21}$$
--   All constants may depend on $\rho$ and $\varepsilon_*$. The maps are linear for each fixed seed.
--
--   For most seeds the linear view $L_uX$ is close to a source of entropy rate above one half; this is the first stage of the sumset seed of Theorem 3.33.
--
--   **Formalization Note** One polynomial-time machine $F$ computes $L_u(z)=F[z,1^u]$ with exactly $M$ output bits; the seed set $\mathbb F_Q$ is $\{0,\dots,Q-1\}$ (its field structure is not used by the statement); the minimum, which is attained, is written as the existence of the minimizing laws $Z_u$.
--
--   Differences from the source:
--   - correction: (3.21) for every n (no large-n clause) → for all n ≥ n₀, with n₀ chosen with the other constants; reason: false at n = 1: ρ = 0.01, ε∗ = 0.1, Pr[X = 0] = 2^{−0.01} gives H∞(X) = ρn; every linear L_u : F_2 → F_2^M with M ≥ 1 yields a point mass or an atom ≈ 0.993, at distance > 0.28 > ε∗ from every law with H∞ ≥ M/2; the proof ends "for sufficiently large n" (p.39)
--   - reading: explicit binary-linear maps L_u, u ∈ F_Q → one polynomial-time machine F with L_u(z) = F [z, 1^u], each L_u F_2-linear with exactly M output bits; reason: explicit = computable by one polynomial-time algorithm (Definition 1.1)
--   - encoding: seed set F_Q; M = Θ_ρ(n); min over Z_u → Fin Q; c₁n ≤ M ≤ c₂n with c₁, c₂ chosen before n; existence of the minimizing family Z_u; reason: the field structure of F_Q is unused; the minimum is attained (compact feasible set)
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.17, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_machineVec

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt

/-- **Theorem 3.17 (Constant-seed linear strong condenser above half), corrected: for all
`n ≥ n₀`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.17, printed p.38 (PDF p.40): "Fix ρ > 0 and a
constant ε∗ > 0. There are constants β > 0, a power of two Q ⩾ 16, and explicit binary-linear maps
Lu : F_2^n → F_2^M, u ∈ F_Q, M = Θρ(n), such that every H∞(X) ⩾ ρn satisfies
(1/Q) Σ_{u∈F_Q} min_{Zu : H∞(Zu) ⩾ (1/2+β/2)M} ∆(LuX, Zu) ⩽ ε∗. (3.21)
All constants may also depend on ε∗. The maps are linear for each fixed seed, not just low-degree
polynomials."

For `ρ > 0` and `ε∗ > 0` there are `β > 0`, a power of two `Q ≥ 16`, constants `c₁, c₂ > 0`, a
threshold `n₀` and one polynomial-time machine `F` such that for every `n ≥ n₀`
there is an output length `M` with `c₁n ≤ M ≤ c₂n`, each map `L_u(z) = F [z, 1^u]` (`u < Q`) outputs
exactly `M` bits and is `𝔽₂`-linear `𝔽₂ⁿ → 𝔽₂^M`, and every source `X` on `𝔽₂ⁿ` with `H∞(X) ≥ ρn` admits
laws `Z_u` on `𝔽₂^M` with `H∞(Z_u) ≥ (1/2 + β/2)M` and `(1/Q) ∑_u Δ(L_u(X), Z_u) ≤ ε∗`.

**Formalization Note.** Correction: the printed statement has no "large n" clause, but is false at
`n = 1` (`ρ = 0.01`, `ε∗ = 0.1`, `Pr[X = 0] = 2^{−0.01}`: every linear `L_u : 𝔽₂ → 𝔽₂^M` with `M ≥ 1`
gives a point mass or a law with an atom `≈ 0.993`, at distance `> 0.28` from every law with
`H∞ ≥ M/2`); its proof ends "for sufficiently large n" (p.39). The only change is `∀ n ≥ n₀`.
The seed set `F_Q` is `{0, …, Q − 1}` (its field structure is not used by the statement), the seed is
given to the machine in unary, and the inner minimum over `Z_u` (attained: the feasible laws form a
compact set) is written as the existence of the minimizing family. `M = Θ_ρ(n)` is `c₁n ≤ M ≤ c₂n`
with constants chosen before `n`. Logarithms are base 2. -/
theorem theorem_3_17 (ρ εstar : ℝ) (hρ : 0 < ρ) (hε : 0 < εstar) :
    ∃ β : ℝ, 0 < β ∧ ∃ Q : ℕ, (∃ j : ℕ, Q = 2 ^ j) ∧ 16 ≤ Q ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ n₀ : ℕ,
        ∃ F : List (List Bool) → List Bool, IsPolyTime F ∧
          ∀ n : ℕ, n₀ ≤ n → ∃ M : ℕ, c₁ * n ≤ M ∧ (M : ℝ) ≤ c₂ * n ∧
            (∀ (u : Fin Q) (z : Fin n → ZMod 2),
              (F [bitsOfVec z, List.replicate u true]).length = M) ∧
            (∀ u : Fin Q, IsLinearMap (ZMod 2)
              (fun z : Fin n → ZMod 2 => machineVec F M [bitsOfVec z, List.replicate u true])) ∧
            ∀ X : PMF (Fin n → ZMod 2), ρ * n ≤ minEntropy X →
              ∃ Z : Fin Q → PMF (Fin M → ZMod 2),
                (∀ u, (1 / 2 + β / 2) * M ≤ minEntropy (Z u)) ∧
                (1 / (Q : ℝ)) * ∑ u : Fin Q,
                    statDist (X.map fun z => machineVec F M [bitsOfVec z, List.replicate u true])
                      (Z u) ≤ εstar := by sorry

end OptTwoSrcExt
