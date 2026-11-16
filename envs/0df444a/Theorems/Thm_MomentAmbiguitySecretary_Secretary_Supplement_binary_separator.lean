-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_binary_separator
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.binary_separator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:53:02.473366+00:00
-- url     : https://prove2.me/theorems/73c4f919-d20e-46ea-85f0-9102ac6d920a
-- title:
--   Theorem 3.1 (companion theorem; not used in the proof of the goal) — Binary separator with disjoint supports, every finite matching moment, all atom bounds and uniform weight decay
-- statement:
--   Fix integers $n,B\ge3$, and set $x_0=1$, $x_1=B$, and $x_j=(nB)^{B^{j-2}}$ for $j\ge2$. The canonical limiting barycentric weights are absolutely summable; their even sum and the sum of their odd absolute values coincide in a positive $W$. The atomic measures
--   $$\nu\{x_j\}=p_j=\begin{cases}w_j/W&j\text{ even},\\0&j\text{ odd},\end{cases}\qquad
--   \mu\{x_j\}=q_j=\begin{cases}|w_j|/W&j\text{ odd},\\0&j\text{ even},\end{cases}$$
--   are probability distributions giving full measure to disjoint even and odd node sets. Every natural moment, including zero, is finite and equal under the two laws. Moreover,
--   $$p_0\ge1-2/n,\quad q_1\ge1-1/(n^2B^2),\quad p_2\ge1/(4n),\quad q_0=p_1=q_2=0,$$
--   $$W\ge n,\qquad |w_j|\le8(nB)^2/x_j^2\quad(j\ge0).$$
--   This fixes the pair used in the later applications to the Section 8.1 construction, rather than assuming a separator with these properties.
--
--   Differences from the source:
--   - encoding: there exist weights and normalized laws, identified by Section 8.1 → the canonical Section 8.1 limiting weights and raw measures satisfy every stated property; reason: naming the witnesses supplied by the source proof changes no parameter instance and avoids an arbitrary separator
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Theorem 3.1, PDF/printed p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Theorem 3.1, supplied preprint, PDF/printed p.7. -/
theorem binary_separator (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) :
    0 < binaryW n B ∧
    binaryW n B = binaryWMinus n B ∧
    Summable (fun j : ℕ => |binaryWeight n B j|) ∧
    IsProbabilityMeasure (binaryNu n B) ∧ IsProbabilityMeasure (binaryMu n B) ∧
    Disjoint (binaryEvenSupport n B) (binaryOddSupport n B) ∧
    binaryNu n B (binaryEvenSupport n B) = 1 ∧
    binaryMu n B (binaryOddSupport n B) = 1 ∧
    (∀ j : ℕ, (binaryNu n B {binaryNode n B j}).toReal = binaryP n B j ∧
      (binaryMu n B {binaryNode n B j}).toReal = binaryQ n B j) ∧
    (∀ s : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ s) (binaryNu n B) ∧
      Integrable (fun x : ℝ≥0 => (x : ℝ) ^ s) (binaryMu n B) ∧
      (∫ x : ℝ≥0, (x : ℝ) ^ s ∂binaryNu n B) =
        (∫ x : ℝ≥0, (x : ℝ) ^ s ∂binaryMu n B)) ∧
    1 - 2 / (n : ℝ) ≤ binaryP n B 0 ∧
    1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤ binaryQ n B 1 ∧
    1 / (4 * (n : ℝ)) ≤ binaryP n B 2 ∧
    binaryQ n B 0 = 0 ∧ binaryP n B 1 = 0 ∧ binaryQ n B 2 = 0 ∧
    (n : ℝ) ≤ binaryW n B ∧
    ∀ j : ℕ, |binaryWeight n B j| ≤ 8 * (n * B : ℝ) ^ 2 / (binaryNode n B j : ℝ) ^ 2 := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
