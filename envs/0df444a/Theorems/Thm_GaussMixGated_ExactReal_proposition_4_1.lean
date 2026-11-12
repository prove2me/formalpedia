-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_proposition_4_1
-- name    : GaussMixGated.ExactReal.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:00.111211+00:00
-- url     : https://prove2.me/theorems/99a81e2d-cac3-45ee-8a42-b960bb119346
-- title:
--   Proposition 4.1 — Compression with a local retention guarantee
-- statement:
--   Fix $C_0>0$. There are an admissible construction program, an admissible oracle-free history evaluator and a universal $C$ with the following property. Let $d,k,D\ge1$, $v>0$ with $vD\le C_0$, $0<\tau<1$, $\xi>0$, $0<\delta'<1$, latent atoms $u_1,\dots,u_s\in\mathbb R^d$ with $s\le k$ and weights $w_i>0$, $\sum_iw_i=1$, and an arbitrary measurable prior history $H_0$ with acceptance $a_0$ and evaluation cost $c_0$. The construction sees only fresh view pairs and evaluations of $H_0$. Put $P=d+k+\tau^{-1}+\xi^{-1}+e^D+\log(1/\delta')+c_0$.
--
--   1. On every outcome the construction halts within $C\,P^C$ work, its description has at most $C\,P^C$ cells, it writes co-isometries $U_h$ with at most $k$ rows, so that $\Phi_h=U_h(\Phi_{h-1}\otimes I_d)$, $\Phi_0=1$, are co-isometries and $e_h\ge0$ ($1\le h\le D$), and the evaluator of the nested histories $H_0\supseteq H_1\supseteq\dots\supseteq H_D$ halts within $C\,P^C$ work on every input.
--   2. With probability at least $1-\delta'$, simultaneously
--
--   $$a_D(u)\ge a_0(u)-\tau\quad\text{for every latent atom with }\|u\|\le1,\qquad(20)$$
--
--   $$\sum_iw_i\,a_D(u_i)\,e_h(u_i)\le2k\xi\quad(1\le h\le D).\qquad(21)$$
--
--   Here $s_h(u)=\|\Phi_hu^{\otimes h}\|^2$ and $e_h(u)=\|u\|^2s_{h-1}(u)-s_h(u)$. The proposition yields a compressed moment representation that keeps nearby atoms while bounding the residual moment of all accepted mass.
--
--   Differences from the source:
--   - reading: 'the finite construction' (batch sizes only as O(·) in the proof) → there exist an admissible construction program and evaluator, for every C₀ > 0, with a universal C; reason: reading 7 of the plan; the strongest existence form
--   - reading: costs polynomial in d, k, τ⁻¹, ξ⁻¹, exp(O(D)), log inverse failure probability and the prior history's evaluation cost → work and description ≤ C·(d + k + τ⁻¹ + ξ⁻¹ + e^D + log(1/δ′) + c₀)^C on every outcome; each H₀ call charged c₀; reason: exp(O(D)) folds into e^D raised to C; deterministic caps on every outcome (§2.3)
--   - encoding: co-isometries Φ_h with at most k rows, Φ_h = U_h(Φ_{h−1} ⊗ I_d) → stage matrices U_h stored in a fixed cell layout with orthonormal rows; Φ_h u^{⊗h} computed by the recursion; reason: the recursive form is the source's construction (PDF p. 12); e_h ≥ 0 is stated as a conclusion
--   - encoding: nested histories obtained by appending gates to H₀ → H_h = H₀ ∩ {the evaluator passes at least h appended gates}, the evaluator's randomness independent of H₀'s; reason: nesting and gate-side-only testing are built in; the source's construction has this form
--   - encoding: with probability at least 1 − (failure probability) → a measurable event inside the success set has measure at least 1 − (failure probability); reason: inner-measure form; never applies a measure to a possibly non-measurable set
--   - encoding: operation count of a terminating procedure → nonterminal work plus one terminal accept charge; reason: each executed instruction costs one unit; the halted state remains fixed without repeated charging
--   - encoding: a finite output description → pointer register 0 at halting is nonnegative and holds the number of description cells; reason: ensures that converting the integer length to a natural number is exact
--   - reading: the exact-real model does not specify the set of program literals → witness programs have rational real literals and contain no reject instruction; reason: the uniform finite algorithms use explicit rational constants or larger rational choices of universal constants; this fixes the literal-set ambiguity without advice in real constants, and rejection is encoded by a terminating fallback
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 11 (printed p. 9), §4 preamble and Proposition 4.1, (20)–(21); recursion Φ_h = U_h(Φ_{h−1} ⊗ I_d) on PDF p. 12 (printed p. 10)

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Machine
import Definitions.Def_GaussMixGated_ExactReal_Jet
import Definitions.Def_GaussMixGated_ExactReal_Mixture
import Definitions.Def_GaussMixGated_ExactReal_Compression

open MeasureTheory

namespace GaussMixGated.ExactReal

/-- Proposition 4.1 (Compression with a local retention guarantee) (Zheng–Xie–He, STOC 2027 #36,
PDF p. 11). For every `C₀ > 0` there are an admissible construction program `Pc`, an admissible
oracle-free history evaluator `Ev` and a universal `C` such that, for view pairs over at most `k`
latent atoms `u_i ∈ ℝ^d` with variance `v`, `vD ≤ C₀`, and an arbitrary prior history `H₀`:
on every outcome `Pc` halts within `C·P^C` work, `P = d + k + τ⁻¹ + ξ⁻¹ + e^D + log(1/δ′) + c₀`,
writes co-isometries `U_h` with at most `k` rows (so `Φ_h = U_h(Φ_{h−1} ⊗ I_d)` are co-isometries
and `e_h ≥ 0`), and `Ev` evaluates the nested histories within `C·P^C` work; with probability at
least `1 − δ′`, (20) `a_D(u) ≥ a_0(u) − τ` for every atom with `‖u‖ ≤ 1` and (21)
`∑_i w_i a_D(u_i) e_h(u_i) ≤ 2kξ` for `1 ≤ h ≤ D`. -/
theorem proposition_4_1 (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ Pc Ev : Program, Admissible Pc ∧ Admissible Ev ∧ OracleFree Ev ∧ ∃ C : ℕ,
    ∀ (d k D : ℕ), 1 ≤ d → 1 ≤ k → 1 ≤ D →
    ∀ (v τ ξ δ' : ℝ), 0 < v → v * D ≤ C₀ → 0 < τ → τ < 1 → 0 < ξ → 0 < δ' → δ' < 1 →
    ∀ (s : ℕ) (w : Fin s → ℝ) (u : Fin s → Fin d → ℝ), IsMixingMeasure k s w →
    ∀ (Ω₀ : Type) [MeasurableSpace Ω₀] (lam₀ : Measure Ω₀), IsProbabilityMeasure lam₀ →
    ∀ (H₀ : (Fin d → ℝ) → Ω₀ → Prop), MeasurableSet {p : (Fin d → ℝ) × Ω₀ | H₀ p.1 p.2} →
    ∀ c₀ : ℕ,
      (∀ (ω₀ : ℕ → Fin s × (Fin d → ℝ) × (Fin d → ℝ)) (ω₁ : ℕ → Ω₀) (g : ℕ → ℝ),
        HaltsWithin Pc (compressionEnv v u H₀ c₀ ω₀ ω₁ g) (compressionStart d k D v τ ξ δ')
          (C * ((d : ℝ) + k + τ⁻¹ + ξ⁻¹ + Real.exp D + Real.log (1 / δ') + c₀) ^ C) ∧
        0 ≤ (final Pc (compressionEnv v u H₀ c₀ ω₀ ω₁ g)
          (compressionStart d k D v τ ξ δ')).ptrs 0 ∧
        (descLen (final Pc (compressionEnv v u H₀ c₀ ω₀ ω₁ g)
            (compressionStart d k D v τ ξ δ')) : ℝ) ≤
          C * ((d : ℝ) + k + τ⁻¹ + ξ⁻¹ + Real.exp D + Real.log (1 / δ') + c₀) ^ C ∧
        (∀ h, 1 ≤ h → h ≤ D →
          IsCoisometryStage (desc (final Pc (compressionEnv v u H₀ c₀ ω₀ ω₁ g)
            (compressionStart d k D v τ ξ δ'))) d k h) ∧
        (∀ h, 1 ≤ h → h ≤ D → ∀ x : Fin d → ℝ,
          0 ≤ compressionResidual (desc (final Pc (compressionEnv v u H₀ c₀ ω₀ ω₁ g)
            (compressionStart d k D v τ ξ δ'))) d k x h) ∧
        (∀ (A : Fin d → ℝ) (g' : ℕ → ℝ),
          HaltsWithin Ev (samplerEnv g')
            (historyStart (desc (final Pc (compressionEnv v u H₀ c₀ ω₀ ω₁ g)
              (compressionStart d k D v τ ξ δ'))) A)
            (C * ((d : ℝ) + k + τ⁻¹ + ξ⁻¹ + Real.exp D + Real.log (1 / δ') + c₀) ^ C))) ∧
      ∃ E : Set ((ℕ → Fin s × (Fin d → ℝ) × (Fin d → ℝ)) × (ℕ → Ω₀) × (ℕ → ℝ)),
        MeasurableSet E ∧
        (∀ ω ∈ E,
          (∀ i, sqNorm (u i) ≤ 1 →
            historyAcceptance Ev (desc (final Pc (compressionEnv v u H₀ c₀ ω.1 ω.2.1 ω.2.2)
                (compressionStart d k D v τ ξ δ'))) v lam₀ H₀ 0 (u i) - τ ≤
              historyAcceptance Ev (desc (final Pc (compressionEnv v u H₀ c₀ ω.1 ω.2.1 ω.2.2)
                (compressionStart d k D v τ ξ δ'))) v lam₀ H₀ D (u i)) ∧
          (∀ h, 1 ≤ h → h ≤ D →
            ∑ i, w i *
              historyAcceptance Ev (desc (final Pc (compressionEnv v u H₀ c₀ ω.1 ω.2.1 ω.2.2)
                (compressionStart d k D v τ ξ δ'))) v lam₀ H₀ D (u i) *
              compressionResidual (desc (final Pc (compressionEnv v u H₀ c₀ ω.1 ω.2.1 ω.2.2)
                (compressionStart d k D v τ ξ δ'))) d k (u i) h ≤ 2 * k * ξ)) ∧
        ENNReal.ofReal (1 - δ') ≤
          ((iidTape (viewPairLaw (d := d) w)).prod ((iidTape lam₀).prod gaussTape)) E := by sorry

end GaussMixGated.ExactReal
