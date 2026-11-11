-- Prove2me | Theorems.Thm_OptAbstention_TLA_theorem_6_2
-- name    : OptAbstention.TLA.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:09:09.119955+00:00
-- url     : https://prove2.me/theorems/75e78a21-9b92-44bb-9d30-5628668df9f7
-- title:
--   Theorem 6.2 (KKMS08): degree-$\ell$ L1 polynomial regression learns to $\mathrm{opt}+\varepsilon$ in $\mathrm{poly}((d+1)^\ell,1/\varepsilon)\log(1/\delta)$ (as printed; insight I2)
-- statement:
--   Let $\ell\in\mathbb N$, $X\subseteq\mathbb R^d$, $\bar D$ a distribution on $X\times\{\pm1\}$ with marginal $D$, $\varepsilon,\delta\in(0,1)$, and $\mathcal C\subseteq\{\pm1\}^X$ such that every $f\in\mathcal C$ has a polynomial $p\in\mathcal P_{d,\ell}$ with $\mathbb E_{x\sim D}|p(x)-f(x)|\le\varepsilon$. Then the degree-$\ell$ L1 polynomial regression algorithm agnostically learns $\mathcal C$ up to error
--   $$\inf_{f\in\mathcal C}\Pr_{(x,y)\sim\bar D}[f(x)\ne y]+\varepsilon$$
--   with failure probability $\delta$, using $\mathrm{poly}((d+1)^\ell,1/\varepsilon)\log(1/\delta)$ samples and time.
--
--   It supplies the classifier $h$ in the first step of the proof of Theorem 6.1.
--
--   **Formalization Note.** One program per $(d,\ell,\varepsilon,\delta)$, chosen before $X$, $\bar D$, $\mathcal C$; it draws labeled examples with `sample` and outputs a degree-$\ell$ polynomial threshold function $x\mapsto\mathrm{sign}(p(x)-t)$, $\mathrm{sign}(0)=+1$, whose error is measured on all of $\bar D$.
--
--   Differences from the source:
--   - encoding: the algorithm's sample complexity and runtime → a program of the randomized sampling real RAM; samples and charged steps both at most C·((d+1)^ℓ/ε)^k·log(1/δ) on every run; reason: the paper names no model; poly((d+1)^ℓ, 1/ε) as C·((d+1)^ℓ/ε)^k is an equivalent family of bounds
--   - reading: 'the degree-ℓ L1 polynomial regression algorithm of [KKMS08]' → one program per (d, ℓ, ε, δ), chosen before X, D̄, C, whose output is a degree-ℓ polynomial threshold function; reason: this is the algorithm's form; letting the program depend on D̄ or C would be the weaker reading
--   - reading: C ⊆ {±1}^X with E_D|p(x) − f(x)| ≤ ε → every f ∈ C measurable, E_D|p − f| a lower Lebesgue integral, infimum in [0,∞]; reason: the expectation and the error are defined only for measurable f; same values
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 13, Theorem 6.2

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Empirical
import Definitions.Def_OptAbstention_TLA_Machine
import Definitions.Def_OptAbstention_TLA_SelectorIO

open MeasureTheory

namespace OptAbstention.TLA

/-- Theorem 6.2 (implicit in KKMS08), p. 13, as printed with `log(1/δ)`: for every `d, ℓ, ε, δ`
one program (the degree-`ℓ` L1 polynomial regression algorithm) that, on every run, draws at most
and runs at most `C·((d+1)^ℓ/ε)^k·log(1/δ)` samples and steps and outputs a degree-`ℓ` polynomial
threshold function, and that for every `X`, every labeled distribution `D̄` and every class `C`
whose members are `ε`-approximated in `L1(D)` by degree-`ℓ` polynomials, has error at most
`opt + ε` except on a set of measure at most `δ`. -/
theorem theorem_6_2 : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (d ℓ : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∃ P : Program,
    Admissible P ∧
    (∀ (ξ : ExStream d) (ν : Tape),
      HaltsWithin P d ξ ν emptyInit
        (C * ((((d : ℝ) + 1) ^ ℓ) / ε) ^ k * Real.log (1 / δ))
        (C * ((((d : ℝ) + 1) ^ ℓ) / ε) ^ k * Real.log (1 / δ))) ∧
    ∀ (X : Set (Pt d)) (Dbar : Measure (X × Bool)) [IsProbabilityMeasure Dbar]
      (Cl : Set (X → ℝ)), IsConceptClass X Cl →
      (∀ f ∈ Cl, ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ ℓ ∧
        ∫⁻ x, ENNReal.ofReal |peval p (x : Pt d) - f x| ∂(Dbar.map Prod.fst) ≤
          ENNReal.ofReal ε) →
      streamLaw Dbar
        {ω | ¬ ∃ St, finalState P d ω.1 ω.2 emptyInit = some St ∧ ValidPTF d ℓ St.cfg.mem ∧
          trainErr Dbar (fun x : X => ptfClassifier d St.cfg.mem (x : Pt d)) ≤
            optTrain Dbar Cl + ENNReal.ofReal ε}
        ≤ ENNReal.ofReal δ := by sorry

end OptAbstention.TLA
