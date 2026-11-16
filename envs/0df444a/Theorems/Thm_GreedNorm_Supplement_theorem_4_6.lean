-- Prove2me | Theorems.Thm_GreedNorm_Supplement_theorem_4_6
-- name    : GreedNorm.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:53:15.029472+00:00
-- url     : https://prove2.me/theorems/b7fc151f-0150-4adb-b032-762041fc8bc3
-- title:
--   Theorem 4.6 — from a good threshold vector, $(2,2\ln n,t)$-bounded fractional and $(3,2\ln n,t)$-bounded integral assignments (corrected: $\max\{1,2\ln n\}$)
-- statement:
--   **Setting (§4.1).** $m\ge1$ machines, $n$ jobs, processing times $p_{ij}\ge0$, nondecreasing left-continuous piecewise-linear $f_i:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$, a monotone symmetric norm $g$; $\mathrm{load}_i(\sigma)=f_i\big(\sum_{j:\sigma(j)=i}p_{ij}\big)$. Fix $\epsilon>0$ and $\mathrm{POS}=\mathrm{POS}_{m,\epsilon}$. A threshold vector $t$ (nonnegative and non-increasing on $\mathrm{POS}$) is **good** if some assignment $\sigma_0$ is $t$-bounded: for every $\ell\in\mathrm{POS}$, at most $\ell-1$ machines have $\mathrm{load}_i(\sigma_0)>t_\ell$. Write $f_i^{-1}(a)=\sup\{z\ge0: f_i(z)\le a\}$.
--
--   **Theorem.** There is a deterministic polynomial-time algorithm that, given the instance and a good threshold vector $t$, outputs, with $\rho=\max\{1,2\ln n\}$:
--
--   1. a fractional assignment $x\ge0$ with $\sum_i x_{ij}\ge1$ for every job $j$ such that for every $\ell\in\mathrm{POS}$
--   $$
--   \#\Big\{i:\ \sum_j x_{ij}p_{ij}>2\,f_i^{-1}(t_\ell)\Big\}\ \le\ \rho\,(\ell-1);
--   $$
--   2. an integral assignment $\sigma$ such that for every $\ell\in\mathrm{POS}$
--   $$
--   \#\Big\{i:\ \sum_{j:\sigma(j)=i}p_{ij}>3\,f_i^{-1}(t_\ell)\Big\}\ \le\ \rho\,(\ell-1).
--   $$
--
--   Formally: one admissible program of the base oracle real RAM, fixed from $\epsilon$ only, halts within $C(n+m+\sum_iK_i+2)^k$ steps on every such input and writes $x$ and $\sigma$ to its output cells.
--
--   The integral assignment is what Corollary 4.7 (Theorem 1.4) turns into an approximation under the doubling condition.
--
--   **Formalization Note** The condition $z>\beta f_i^{-1}(a)$ is written $f_i(z/\beta)>a$, equivalent for nondecreasing left-continuous $f_i$ including when the set in the supremum is empty or unbounded. Input: the layout with $t$ and the flags of $\mathrm{POS}$; output: real cell $in+j$ holds $x_{ij}$, integer cell $2+j$ holds $\sigma(j)$. $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - correction: count factor 2 ln n → count factor max{1, 2 ln n}; reason: at n = 1 the printed factor is 0; counterexample n = 1, m = 2 (POS = {1, 2}), p_11 = p_21 = 1, f_1 = f_2 = id, t_1 = 1, t_2 = 0: t is good (job on machine 1), but every fractional or integral assignment puts positive load on some machine, so at ℓ = 2 one machine exceeds 0 = 2 ln 1 · (2 − 1); for n ≥ 2, 2 ln n > 1
--   - reading: (2, 2 ln n, t)- and (3, 2 ln n, t)-bounded (the paper's synonym for Definition 4.4's "-constrained"), with Definition 4.4 ordering the tuple (ρ, β, t) → 2 (resp. 3) multiplies f_i^{-1}(t_ℓ) and 2 ln n multiplies ℓ − 1; reason: the proof (Eq. (1), Claim 4.5, Eq. (2)) and Corollary 4.7 use this order; the literal Definition 4.4 order is supported by no line of the paper
--   - encoding: Σ_j x_ij p_ij > β · f_i^{-1}(t_ℓ), f_i^{-1}(a) = sup{z | f_i(z) ≤ a} → t_ℓ < f_i((Σ_j x_ij p_ij)/β); reason: equivalent for nondecreasing left-continuous f_i on [0, ∞) and β > 0, also when the set is empty or unbounded; avoids a real sSup
--   - encoding: nondecreasing left-continuous piecewise-linear f_i : ℝ≥0 → ℝ≥0 → explicit PWL data (breakpoints, affine pieces), left-continuous by construction, with hypotheses MonotoneOn on [0, ∞) and nonnegativity on [0, ∞); reason: the algorithm must read f_i; every such function has this form
--   - encoding: we can efficiently find → one admissible GreedNorm.Machine program, chosen from ϵ before the instance, halting within C(n + m + Σ_i K_i + 2)^k steps with x and σ in its output cells; t and the index set POS in the input; reason: deterministic polynomial time on the base machine model; g is the outer oracle
--   - encoding: m machines → 0 < m; reason: POS and threshold vectors are defined for m ≥ 1; with m = 0 and n ≥ 1 no assignment exists
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 4.6, Definition 4.4, Eqs. (1)–(2), p.12 (PDF 14); §4.1, p.11 (PDF 13); Definition 2.2 and Definition 3.3 (good), pp.5–6 (PDF 7–8)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_GreedNorm_glbLoad
import Definitions.Def_GreedNorm_POS
import Definitions.Def_GreedNorm_IsThreshold
import Definitions.Def_GreedNorm_IsTBoundedVec
import Definitions.Def_GreedNorm_Machine
import Definitions.Def_GreedNorm_Supplement_PWL
import Definitions.Def_GreedNorm_Supplement_pwlNorm
import Definitions.Def_GreedNorm_Supplement_pwlThreshInitState

namespace GreedNorm.Supplement

/-- **Theorem 4.6: from a good threshold vector, an efficient `(2, 2 ln n, t)`-bounded fractional and
`(3, 2 ln n, t)`-bounded integral assignment** (corrected: factor `max{1, 2 ln n}`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), Theorem 4.6, p.12 (PDF 14): "Let t be a good threshold vector, then we can efficiently find a
(2, 2 ln n, t)-bounded fractional assignment, and a (3, 2 ln n, t)-bounded integral assignment",
with Definition 4.4 and Eqs. (1)–(2), p.12 (PDF 14), and the setting of §4.1, p.11 (PDF 13).

Fix `ϵ > 0` (so `POS = POS_{m,ϵ}`). There are one admissible program `P` of `GreedNorm.Machine`
and constants `C, k` such that for every piecewise-linear GLB instance (`m ≥ 1`, `p ≥ 0`,
explicit `f_i` nondecreasing and nonnegative on `[0, ∞)`, `g` a monotone symmetric norm) and
every good threshold vector `t` (a threshold vector for which some assignment `σ₀` is
`t`-bounded: for every `ℓ ∈ POS` at most `ℓ − 1` machines have `f_i(Σ_{σ₀(j)=i} p_ij) > t_ℓ`),
the run of `P` halts within `C (n + m + Σ_i K_i + 2)^k` steps and outputs, with
`ρ = max{1, 2 ln n}`,
1. a fractional assignment `x ≥ 0` with `Σ_i x_ij ≥ 1` for every job `j` such that for every
   `ℓ ∈ POS` at most `ρ (ℓ − 1)` machines have `Σ_j x_ij p_ij > 2 f_i^{-1}(t_ℓ)`;
2. an integral assignment `σ` such that for every `ℓ ∈ POS` at most `ρ (ℓ − 1)` machines have
   `Σ_{j:σ(j)=i} p_ij > 3 f_i^{-1}(t_ℓ)`.

**Formalization Note** `z > β f_i^{-1}(a)` with `f_i^{-1}(a) = sup{z ≥ 0 | f_i(z) ≤ a}` is written
`a < f_i(z / β)`; the two agree for nondecreasing left-continuous `f_i`, also when the set is
empty or all of `[0, ∞)`, and no real `sSup` is used. Input layout
`Supplement.pwlThreshInitState ε p D t` (the instance, `t ℓ` and the flag `ℓ ∈ POS` for
`ℓ ≤ m`); inner oracle `Supplement.pwlNorm D`, outer oracle `g`. Output: on halting, real cell
`i * n + j` holds `x i j` and integer cell `2 + j` holds `σ(j)`. The tuple is read as the proof
and Corollary 4.7 use it: `2` (resp. `3`) multiplies `f_i^{-1}(t_ℓ)` and `2 ln n` multiplies
`ℓ − 1`. At `n = 1` the printed factor `0` is false, hence `max{1, ·}`. -/
theorem theorem_4_6 (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C k : ℕ,
      ∀ (n m : ℕ), 0 < m → ∀ (p : Fin m → Fin n → ℝ), (∀ i j, 0 ≤ p i j) →
      ∀ (D : Fin m → Supplement.PWL),
        (∀ i, MonotoneOn (D i).eval (Set.Ici 0)) →
        (∀ i (z : ℝ), 0 ≤ z → 0 ≤ (D i).eval z) →
      ∀ (g : (Fin m → ℝ) → ℝ), SymNormLoad.IsMonotoneSymmetricNorm g →
      ∀ (t : ℕ → ℝ), IsThreshold m ε t →
        (∃ σ₀ : Fin n → Fin m, IsTBoundedVec ε t (glbLoad p (Supplement.pwlNorm (n := n) D) σ₀)) →
        ∃ T : ℕ, T ≤ C * (n + m + ∑ i, (D i).K + 2) ^ k ∧
          (Machine.run P (Supplement.pwlNorm (n := n) D) g
            (Supplement.pwlThreshInitState ε p D t) T).halted = true ∧
          ∃ (x : Fin m → Fin n → ℝ) (σ : Fin n → Fin m),
            (∀ (i : Fin m) (j : Fin n), (Machine.run P (Supplement.pwlNorm (n := n) D) g
              (Supplement.pwlThreshInitState ε p D t) T).core.mem
                ((i : ℤ) * (n : ℤ) + (j : ℤ)) = x i j) ∧
            (∀ j : Fin n, (Machine.run P (Supplement.pwlNorm (n := n) D) g
              (Supplement.pwlThreshInitState ε p D t) T).integerMemory
                (2 + (j : ℤ)) = ((σ j : ℕ) : ℤ)) ∧
            (∀ i j, 0 ≤ x i j) ∧ (∀ j, 1 ≤ ∑ i, x i j) ∧
            (∀ ℓ ∈ POS m ε,
              (((Finset.univ.filter fun i : Fin m =>
                  t ℓ < (D i).eval ((∑ j, x i j * p i j) / 2)).card : ℕ) : ℝ) ≤
                max 1 (2 * Real.log (n : ℝ)) * ((ℓ : ℝ) - 1)) ∧
            (∀ ℓ ∈ POS m ε,
              (((Finset.univ.filter fun i : Fin m =>
                  t ℓ < (D i).eval
                    ((∑ j ∈ Finset.univ.filter (fun j => σ j = i), p i j) / 3)).card : ℕ) : ℝ) ≤
                max 1 (2 * Real.log (n : ℝ)) * ((ℓ : ℝ) - 1)) := by sorry

end GreedNorm.Supplement
