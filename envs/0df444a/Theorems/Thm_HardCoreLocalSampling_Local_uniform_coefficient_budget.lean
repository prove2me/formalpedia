-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_uniform_coefficient_budget
-- name    : HardCoreLocalSampling.Local.uniform_coefficient_budget
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:55.857209+00:00
-- url     : https://prove2.me/theorems/cc193403-ca35-40db-a809-b8d9ee95ede9
-- title:
--   Theorem 4 — A uniform coefficient budget for centered recursions
-- statement:
--   Let $b\ge1$, let $S$ be a finite acyclic family of states, each with an ordered list of $d_s\le b$ children, and real messages with $y_s=F_s(y_{s_1},\ldots,y_{s_{d_s}})$. Let positive rational $r,M$ and rational $0\le\rho<1$ be uniform over the family, $g=1-\rho$. For rational centers $c_s$, write $\mathbf c_s=(c_{s_1},\dots,c_{s_{d_s}})$ and assume:
--
--   1. $F_s$ is holomorphic on a neighborhood of the closed polydisc $|w_i-c_{s_i}|\le r$, bounded in modulus by $M$ there, with real Taylor coefficients at $\mathbf c_s$;
--   2. $\sum_i|\partial_iF_s(\mathbf c_s)|\le\rho$;
--   3. $|y_s-c_s|\le\tau$ and $|F_s(\mathbf c_s)-c_s|\le(1+\rho)\tau$.
--
--   Let positive rational $\eta,\tau$ satisfy, with $t=\eta/r$,
--
--   $$
--   t\le\frac12,\qquad\frac M\eta\bigl[bt(1-t)^{-b-1}-bt\bigr]\le\frac g8,\qquad\tau\le\frac{\eta g}{16(1+\rho)}.
--   $$
--
--   Then $z_s=(y_s-c_s)/\eta$ has an expansion $z_s=\sum_{\alpha\in\mathbb N^{d_s}}d_{s,\alpha}\prod_iz_{s_i}^{\alpha_i}$, absolutely convergent on $[-1,1]^{d_s}$, with rational envelopes $q_{s,\alpha}\ge|d_{s,\alpha}|$ satisfying
--
--   $$
--   \sum_\alpha q_{s,\alpha}\le\rho+\frac{5g}{16}<1,\qquad\sum_\alpha|\alpha|q_{s,\alpha}\le\rho+\frac g4<1.
--   $$
--
--   The envelopes have a uniform exponential degree tail, and are effectively computable if certified approximations of the constant and first-order Taylor coefficients are available.
--
--   Differences from the source:
--   - reading: bounded in modulus by M there → the bound is assumed on the closed polydisc only; reason: the antecedent of there is ambiguous between the polydisc and its neighborhood; this is the weaker hypothesis and so the stronger theorem
--   - encoding: rational envelopes, effectively computable given certified low-order approximations → one Computable function maps the parameters and any rational approximations at a computed precision to q_{s,α}, and the bounds hold for every such approximation; reason: since approximations exist at every precision this contains the existence claim, and it is the source's effectivity condition in finite form
--   - encoding: a uniform exponential degree tail → C and θ are chosen from the parameters before the family and bound the mass of each total degree; reason: this is uniformity over the family with these parameters
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Theorem 4, printed p.4 (PDF p.5)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Theorem 4, printed p.4 (PDF p.5).
A generic statement about finite acyclic families of holomorphic recursions, not only the
hard-core one. The envelopes are computed from the parameters and from any certified rational
approximations of the constant and first-order Taylor coefficients, and `C, θ` give the uniform
exponential degree tail over all families with these parameters. -/
theorem uniform_coefficient_budget :
    ∃ (prec : Thm4Code → ℕ) (env : Thm4Code × RatCode × List RatCode × List ℕ → RatCode),
      Computable prec ∧ Computable env ∧
      ∀ (b : ℕ) (r M rho eta tau : ℚ), 1 ≤ b → 0 < r → 0 < M → 0 ≤ rho → rho < 1 → 0 < eta → 0 < tau →
        eta / r ≤ 1 / 2 →
        middleExpr b M eta (eta / r) ≤ (1 - rho) / 8 →
        tau ≤ eta * (1 - rho) / (16 * (1 + rho)) →
        let code : Thm4Code := (b, codeOfRat r, codeOfRat M, codeOfRat rho, codeOfRat eta,
          codeOfRat tau)
        ∃ (C θ : ℝ), 0 ≤ C ∧ 0 ≤ θ ∧ θ < 1 ∧
        ∀ {S : Type} [Fintype S] (deg : S → ℕ) (child : ∀ s, Fin (deg s) → S) (rank : S → ℕ)
          (F : ∀ s, (Fin (deg s) → ℂ) → ℂ) (y : S → ℝ) (c : S → ℚ),
          (∀ s, deg s ≤ b) →
          (∀ s i, rank (child s i) < rank s) →
          (∀ s, F s (fun i => (y (child s i) : ℂ)) = (y s : ℂ)) →
          (∀ s, ∃ W : Set (Fin (deg s) → ℂ), IsOpen W ∧
            polydisc (fun i => ((c (child s i) : ℝ) : ℂ)) (r : ℝ) ⊆ W ∧
            DifferentiableOn ℂ (F s) W) →
          (∀ s, ∀ z ∈ polydisc (fun i => ((c (child s i) : ℝ) : ℂ)) (r : ℝ),
            ‖F s z‖ ≤ (M : ℝ)) →
          (∀ s α, (taylorCoeff (F s) (fun i => ((c (child s i) : ℝ) : ℂ)) α).im = 0) →
          (∀ s, ∑ i, ‖partialD i (F s) (fun i => ((c (child s i) : ℝ) : ℂ))‖ ≤ (rho : ℝ)) →
          (∀ s, |y s - (c s : ℝ)| ≤ (tau : ℝ)) →
          (∀ s, |(F s (fun i => ((c (child s i) : ℝ) : ℂ))).re - (c s : ℝ)| ≤
            (1 + (rho : ℝ)) * (tau : ℝ)) →
          ∀ s,
            let A : (Fin (deg s) → ℕ) → ℝ := fun α =>
              (taylorCoeff (F s) (fun i => ((c (child s i) : ℝ) : ℂ)) α).re
            let D := normalizedCoeff (eta : ℝ) (c s : ℝ) A
            let z : S → ℝ := fun u => (y u - (c u : ℝ)) / (eta : ℝ)
            (∀ x : Fin (deg s) → ℝ, (∀ i, |x i| ≤ 1) →
              Summable fun α => |D α * monomial x α|) ∧
            HasSum (fun α => D α * monomial (fun i => z (child s i)) α) (z s) ∧
            ∀ (a0 : ℚ) (a1 : Fin (deg s) → ℚ),
              |(a0 : ℝ) - A 0| ≤ (1 / 2 : ℝ) ^ prec code →
              (∀ i, |(a1 i : ℝ) - A (Pi.single i 1)| ≤ (1 / 2 : ℝ) ^ prec code) →
              let q : (Fin (deg s) → ℕ) → ℚ := fun α =>
                ratOfCode (env (code, codeOfRat a0, (List.ofFn a1).map codeOfRat, List.ofFn α))
              (∀ α, |D α| ≤ (q α : ℝ)) ∧
              Summable (fun α => (q α : ℝ)) ∧
              ∑' α, (q α : ℝ) ≤ (rho : ℝ) + 5 * (1 - (rho : ℝ)) / 16 ∧
              Summable (fun α => (mdeg α : ℝ) * (q α : ℝ)) ∧
              ∑' α, (mdeg α : ℝ) * (q α : ℝ) ≤ (rho : ℝ) + (1 - (rho : ℝ)) / 4 ∧
              ∀ k, ∑ α ∈ Finset.Nat.antidiagonalTuple (deg s) k, (q α : ℝ) ≤ C * θ ^ k := by sorry

end HardCoreLocalSampling.Local
