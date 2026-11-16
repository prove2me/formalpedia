-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_learn_tree_sparsifier
-- name    : LeeCutCertificates.Certificate.Supplement.learn_tree_sparsifier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:07:44.565205+00:00
-- url     : https://prove2.me/theorems/bf5b5c7e-e859-485d-ac6a-523aec19426e
-- title:
--   Theorem 7 — Learning a tree cut sparsifier
-- statement:
--   Set $C_0=3433597776$. There is an absolute positive constant $C$, fixed before every public input, such that for each $n\ge2$ and every real parameter
--
--   $$C_0\ln^2(2n)(\ln\ln(2n))^2\le\alpha\le\sqrt n,$$
--
--   one deterministic program works for every nonnegative graph $G$ with $\lambda(G)>0$. It returns a safe partition $P$ preserving every original minimum cut and an explicit $\alpha$-tree cut sparsifier $T$ of $G/P$, with at most $8n$ nodes. Its query count, on every answer function, is at most
--
--   $$C\,\frac{n^2}{\alpha}L(n)^3K(n)^2.$$
--
--   The output approximates every quotient shore with distortion at most the supplied real $\alpha$. This companion theorem is independent of the certificate proof.
--
--   **Formalization Note** $C_0=2\cdot3892968\cdot9\cdot49$ follows from §11.7 and Appendix A, printed p.54 (PDF p.55): $L\le3\ln(2n)$ and $K\le7\ln\ln(2n)$. The phase integer is a floor of $\alpha/(3892968L(N)^2K(N)^2)$, without restricting $\alpha$ to integers. The cap retains the full rate and is uniform in weights, $\alpha$ and output size.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - encoding: there exists an absolute lower-threshold constant and a big-O query constant → the fixed natural-log threshold C₀=3433597776 and an absolute C before n and α for C n² L³ K²/α; reason: the source integer threshold and L,K bounds give C₀; §11.7 sums the phase costs uniformly
--   - encoding: a partition into nonempty blocks and its quotient → a surjective Fin-labeled block map, contracted endpoint records and explicit safety for every optimum; reason: block labels and retained loops change no cut weight
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Theorem 7, printed p.12 (PDF p.13); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Quotients
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem learn_tree_sparsifier :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (α : ℝ),
      learningThreshold n ≤ α → α ≤ Real.sqrt n →
      ∃ p : OracleProgram (Finset (Fin n)) (LearnedTree n),
        p.Capped (C * (n : ℝ) ^ 2 / α * logL n ^ 3 * logK n ^ 2) ∧
        ∀ (m : ℕ) (G : Graph n m), Nonnegative G → 0 < lam G →
          CorrectLearnedTree G α (p.run (cutw G)).1 := by sorry

end LeeCutCertificates.Certificate.Supplement
