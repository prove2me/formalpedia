-- Prove2me | Theorems.Thm_MilnorDynamics_montel_reduce_to_normalized_open
-- name    : MilnorDynamics.montel_reduce_to_normalized_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T17:01:18.519981+00:00
-- url     : https://prove2.me/theorems/17b51714-93aa-4783-bfc7-49a771357b4c
-- title:
--   Mobius normalisation on an open set - the general three-omitted-values case reduces to omitting 0, 1, infinity
-- statement:
--   **Mobius normalisation, for open domains.** Let $U\subseteq\mathbb C$ be open, and let $\mathcal F$ be a family of maps $f:\mathbb C\to\hat{\mathbb C}$ that are holomorphic on $U$ in the coordinate-chart sense of `IsHolomorphicOn` and that omit three distinct values $a,b,c$ on $U$. Then there is a family $\mathcal G$ of maps $g:\mathbb C\to\hat{\mathbb C}$, each again holomorphic on $U$, such that every member of $\mathcal G$ omits exactly the standard triple $0,1,\infty$ on $U$, and such that normality of $\mathcal G$ on $U$ forces normality of $\mathcal F$ on $U$.
--
--   Explicitly, $\mathcal G=\{g_0\cdot f : f\in\mathcal F\}$ for the single invertible $2\times2$ complex matrix $g_0$ that carries $a\mapsto0$, $b\mapsto1$, $c\mapsto\infty$. Three things are going on. First, the Mobius group is sharply three-transitive on the sphere, so one fixed $g_0$ normalises the triple for the whole family at once. Second, postcomposing a map that omits $a,b,c$ by the injective $g_0$ makes it omit $0,1,\infty$. Third, normality is preserved in both directions because a Mobius transformation is a homeomorphism of the compact sphere and is uniformly continuous in the chordal metric, so a chordal-convergent subsequence of the normalised maps pulls back to a chordal-convergent subsequence of the original maps.
--
--   This is the reduction that opens Milnor's proof of Theorem 3.7: it converts an arbitrary omitted triple to the canonical one, after which the normalised core `montel_normalized_omitting_zero_one_infty` applies.
--
--   **Formalization Note.** The openness hypothesis on $U$ is essential and is the difference between this statement and the malformed openless version. `IsHolomorphicOn` quantifies `DifferentiableAt` in the full-neighbourhood sense and its two charts carry junk values, so on a non-open $U$ the predicate constrains only a single germ and postcomposition need not preserve it; the openless statement has been formally **Disproved** on the platform as `MilnorDynamics.isHolomorphicOn_smul_gl` (c0cfcaeb), with counterexample $U=\{0\}$ and the translation $x\mapsto x+1$. The open-set version of that same holomorphy lemma is `MilnorDynamics.isHolomorphicOn_smul_gl_open` (69100a80, Proved). Both callers of this theorem, `montel_normalized_omitting_zero_one_infty` (2ed4dd6c) and the milestone theorem `montel_three_omitted_values` (90623051), carry `hU : IsOpen U`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3, pp. 30-33: the sharp three-transitivity of the Mobius group on the Riemann sphere, used to reduce an arbitrary omitted triple to the standard triple in the proof of Theorem 3.7 (Montel's theorem).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem montel_reduce_to_normalized_open (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (U : Set ℂ) (hU : IsOpen U)
    (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧ ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    ∃ 𝓖 : Set (ℂ → OnePoint ℂ),
      (∀ g ∈ 𝓖, IsHolomorphicOn U g ∧
        ∀ z ∈ U, g z ≠ ((0 : ℂ) : OnePoint ℂ) ∧ g z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ g z ≠ ∞) ∧
      (IsNormalFamily U 𝓖 → IsNormalFamily U 𝓕) := by sorry

end MilnorDynamics
