-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_Supplement_theorem_3_1
-- name    : FourierSparseTesting1656.Uniform.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:13:35.897661+00:00
-- url     : https://prove2.me/theorems/f8ade102-8dd5-44d7-974d-945d1bd9a7d5
-- title:
--   Theorem 3.1 — SpectrumTest is nonadaptive with $O(s^4)$ queries, rejects $f\in F_s$ w.p. $\le 1/16$ and $\varepsilon$-far $f$ w.p. $\ge\varepsilon/8$
-- statement:
--   Fix $n\ge0$, an integer $s\ge1$ and $\varepsilon\in(0,1)$. Let $F_s$ be the class of Boolean functions $f:\mathbb F_2^n\to\{-1,+1\}$ with at most $s$ nonzero Fourier coefficients, and $\operatorname{dist}(f,F_s)$ the minimum, over $g\in F_s$, of the fraction of points where $f$ and $g$ differ. Then SpectrumTest (Algorithm 1), which draws a uniform subspace $H$ of dimension $d=\min\{n,\lceil\log_2(16s^4)\rceil\}$, a complement $W$ of $H^\perp$, and independent uniform shifts $a,r\in\mathbb F_2^n$, is nonadaptive, uses
--   $$O(s^4)$$
--   oracle queries, and satisfies:
--
--   1. **Completeness.** If $f\in F_s$, the algorithm rejects with probability at most $1/16$.
--   2. **Soundness.** If $\operatorname{dist}(f,F_s)\ge\varepsilon$, the algorithm rejects with probability at least $\varepsilon/8$.
--
--   This is the query-inefficient first tester of the paper: it reads the whole restriction of $f$ to four cosets of $H$ and checks the identities that the restricted spectra of a sparse function satisfy. Its soundness rests on the fixed-subspace bound $\operatorname{dist}(f,F_s)\le 8p_H(f)$ (Proposition 3.8).
--
--   **Formalization Note** The statement is about the defined algorithm `spectrumTest n s Wsel`, an instance of the referenced nonadaptive query model, and holds for every rule `Wsel` assigning to each subspace $H$ a complement of $H^\perp$. It asserts, for one absolute constant $C>0$ chosen before $n,s,\varepsilon$: every run makes at most $\lceil Cs^4\rceil$ queries; on every $f$ and every seed $(H,a,r)$ the output is $1$ if the four checks of Algorithm 1 pass for $f$ at $H$, $W$, $a$, $r$ and $0$ otherwise; and the two rejection bounds, where "rejects" is the event that the output is $0$ and probabilities are under the uniform law of $(H,a,r)$.
--
--   Differences from the source:
--   - encoding: Boolean f : F₂ⁿ → {−1,+1} → bit function f : (Fin n → ZMod 2) → Bool with false ↦ +1, true ↦ −1; reason: bijective encoding; oracle answers are the bits
--   - encoding: "uses O(s⁴) oracle queries" → one absolute constant C > 0 quantified before n, s, ε; the query list has length at most ⌈C·s⁴⌉ on every seed; reason: the source's constant is absolute (the proof on p. 15 gives 4·2^d ≤ 128 s⁴); the ceiling only rounds a real bound for a natural count
--   - encoding: "SpectrumTest is nonadaptive" → spectrumTest is a CyclicForrelation.Even.NonadaptiveAlgorithm whose queries depend only on the seed and whose output depends only on the seed and the answers, and the theorem states that this output is 1 exactly when the checks of Algorithm 1 pass for f (0 otherwise); reason: nonadaptivity is structural in the model; the decision clause records that the object is Algorithm 1 and changes no instance
--   - reading: "a complement W with F₂ⁿ = W ⊕ H⊥" (choice unspecified) → the theorem holds for every fixed rule Wsel choosing a complement of H⊥ for each H; reason: the source does not say how W is chosen; every deterministic rule is covered, and any randomized choice independent of a, r is a mixture of such rules, so this is the strongest reading
--   - encoding: d = min{n, ⌈log₂(16s⁴)⌉}, H uniform d-dimensional, a, r independent uniform → specDim n s = min n (Nat.clog 2 (16 s⁴)); the seed (H, a, r) is uniform on {H : dim H = d} × F₂ⁿ × F₂ⁿ; reason: Nat.clog 2 N is ⌈log₂ N⌉ for the integer N = 16s⁴; the uniform law on the product is the independent uniform choice
--   - encoding: dist(f, F_s) = min over F_s; F_k defined for k ≤ 2ⁿ → distToSet f (Fs n s), with Fs n s defined by the same formula for every s; reason: F_s is finite and contains the constants, so the infimum is the minimum; for s ≥ 2ⁿ the class is all Boolean functions, as in the published goal
--   - encoding: "rejects with probability at most 1/16" / "at least ε/8" → the seed law (an ENNReal-valued probability measure) of the event {σ | runAlgorithm (spectrumTest n s Wsel) f σ = 0} is ≤ ENNReal.ofReal (1/16), resp. ≥ ENNReal.ofReal (ε/8); reason: reject is output 0 (the output is in {0,1} by the decision clause); the values are probabilities in [0,1], so the ENNReal comparison is the real one
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 8, Theorem 3.1 (Algorithm 1, p. 8; completeness §3.1, pp. 8–9; soundness §3.2 and Proposition 3.8, pp. 10–15; query complexity p. 15); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Supplement_SpectrumTest

set_option autoImplicit false
open FourierDimTesting102.Quantum CyclicForrelation.Even FourierSparseTesting1656.Uniform

namespace FourierSparseTesting1656.Uniform.Supplement

/-- Theorem 3.1, p.8: there is an absolute constant `C > 0` such that for every `n ≥ 0`, integer
`s ≥ 1`, `ε ∈ (0,1)` and every rule `Wsel` choosing a complement of `H^⊥`, SpectrumTest
(Algorithm 1, `spectrumTest n s Wsel`, a nonadaptive query algorithm by construction)
1. makes at most `⌈C s⁴⌉` queries on every seed;
2. on every `f` and seed `(H, a, r)` accepts (outputs `1`) exactly when the four checks of
   Algorithm 1 pass for `f`, and rejects (outputs `0`) otherwise;
3. (completeness) rejects every `f ∈ F_s` with probability at most `1/16`;
4. (soundness) rejects every `f` with `dist(f, F_s) ≥ ε` with probability at least `ε/8`,
probabilities over a uniform `d`-dimensional `H`, `d = min{n, ⌈log₂(16s⁴)⌉}`, and independent
uniform `a, r ∈ F₂ⁿ`. -/
theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n s : ℕ) (ε : ℝ), 1 ≤ s → 0 < ε → ε < 1 →
        ∀ Wsel : Submodule (ZMod 2) (V n) → Submodule (ZMod 2) (V n),
          (∀ H : Submodule (ZMod 2) (V n), IsComplementOfPerp H (Wsel H)) →
          CostAtMost (spectrumTest n s Wsel) ⌈C * (s : ℝ) ^ 4⌉₊ ∧
          (∀ (f : BoolFn n) (σ : SpecSeed n s),
            runAlgorithm (spectrumTest n s Wsel) f σ =
              @ite ℝ (checksPass s σ.1.1 (Wsel σ.1.1) f σ.2.1 σ.2.2) (Classical.dec _) 1 0) ∧
          (∀ f ∈ Fs n s,
            (spectrumTest n s Wsel).law {σ | runAlgorithm (spectrumTest n s Wsel) f σ = 0} ≤
              ENNReal.ofReal (1 / 16)) ∧
          (∀ f : BoolFn n, ε ≤ distToSet f (Fs n s) →
            ENNReal.ofReal (ε / 8) ≤
              (spectrumTest n s Wsel).law {σ | runAlgorithm (spectrumTest n s Wsel) f σ = 0}) := by sorry

end FourierSparseTesting1656.Uniform.Supplement
