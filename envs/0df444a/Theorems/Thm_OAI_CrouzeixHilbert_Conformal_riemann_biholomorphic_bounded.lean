-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Conformal_riemann_biholomorphic_bounded
-- name    : OAI.CrouzeixHilbert.Conformal.riemann_biholomorphic_bounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:33:50.829982+00:00
-- url     : https://prove2.me/theorems/134e3a22-80f5-4a52-b17b-35b93a9d137d
-- title:
--   Riemann mapping theorem for bounded simply connected open sets, with a holomorphic inverse and nonvanishing derivatives
-- statement:
--   Let $U \subseteq \mathbb C$ be an open set (`IsOpen U`) that is bounded (`Bornology.IsBounded U`) and simply connected in Mathlib's sense (`IsSimplyConnected U`: $U$ is path-connected and every loop in $U$ is homotopic in $U$ to a constant loop; in particular $U$ is nonempty), and let $a \in U$. Let $\mathbb D = \{w : |w| < 1\}$ (`ball 0 1`). Then there are functions $f, g : \mathbb C \to \mathbb C$ such that
--   - $f$ is complex differentiable on $U$ and $g$ is complex differentiable on $\mathbb D$ (`DifferentiableOn ℂ`);
--   - $f$ maps $U$ bijectively onto $\mathbb D$ and $g$ maps $\mathbb D$ bijectively onto $U$ (`BijOn`);
--   - $g$ and $f$ are inverse to each other between $U$ and $\mathbb D$ (`InvOn g f U (ball 0 1)`: $g(f(z)) = z$ for $z \in U$ and $f(g(w)) = w$ for $w \in \mathbb D$);
--   - $f(a) = 0$;
--   - $f'(z) \ne 0$ for every $z \in U$ and $g'(w) \ne 0$ for every $w \in \mathbb D$ (`deriv`).
--
--   $$\exists\, f, g:\quad f : U \xrightarrow{\ \sim\ } \mathbb D,\ \ g = f^{-1} : \mathbb D \xrightarrow{\ \sim\ } U \text{ holomorphic},\quad f(a) = 0,\quad f' \ne 0 \text{ on } U,\ g' \ne 0 \text{ on } \mathbb D.$$
--
--   This is the Riemann mapping theorem (B. Riemann, 1851; first proved completely by P. Koebe and C. Carathéodory, 1912) for bounded simply connected open sets, stated with Mathlib's homotopy notion of simple connectivity.
--
--   Lean: `OAI.CrouzeixHilbert.Conformal.riemann_biholomorphic_bounded`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/Univalent.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle. A Riemann mapping theorem is already published and Proved on this platform as `AhlforsComplexAnalysis.riemann_mapping_theorem` (4c8c47ca). The two are comparable, and neither contains the other. That statement allows unbounded regions $\Omega \ne \mathbb C$ and adds uniqueness of the normalized map, but it reads simple connectivity as connectedness of the complement in the extended plane (`IsSimplyConnectedRegion`), and it does not state that the inverse is holomorphic or that the derivatives never vanish. This statement needs boundedness and uses Mathlib's `IsSimplyConnected`, and passing between the two notions of simple connectivity is a theorem of plane topology in its own right.
-- source:
--   B. Riemann, Grundlagen für eine allgemeine Theorie der Functionen einer veränderlichen complexen Grösse (1851) (the theorem); first complete proofs by P. Koebe and C. Carathéodory (1912); proof by the extremal problem of L. Fejér and F. Riesz (T. Radó, 1923) with Koebe's square-root trick; proof and Lean code: OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/Univalent.lean (declaration OAI.CrouzeixHilbert.Conformal.riemann_biholomorphic_bounded)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem riemann_biholomorphic_bounded {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U) :
    ∃ f g : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f U (ball 0 1) ∧ BijOn g (ball 0 1) U ∧
      InvOn g f U (ball 0 1) ∧ f a = 0 ∧
      (∀ z ∈ U, deriv f z ≠ 0) ∧ (∀ w ∈ ball 0 1, deriv g w ≠ 0) := by
  sorry

end CrouzeixHilbert.Conformal

end

end OAI
end
