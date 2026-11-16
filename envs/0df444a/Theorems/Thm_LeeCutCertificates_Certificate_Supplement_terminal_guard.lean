-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_terminal_guard
-- name    : LeeCutCertificates.Certificate.Supplement.terminal_guard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:21.093839+00:00
-- url     : https://prove2.me/theorems/e2b7ab59-ec0e-4dde-bf12-23f52450c4c0
-- title:
--   Lemma 26 — A graph approximating the terminal cuts of a tree
-- statement:
--   For a known nonnegative capacitated hierarchy tree $T$ on $n\ge2$ terminals with childless terminals, there is a single deterministic offline choice of a nonnegative explicit graph $J_{\rm prot}(T)$ on those terminals such that
--
--   $$R_T(S)\le c_{J_{\rm prot}}(S)\le42R_T(S)\qquad(S\subseteq V).$$
--
--   The graph is a function of the known tree and its capacities alone, with no hidden graph or cut-oracle input. It therefore uses zero queries to $G$. Quality $\rho_0=42$ is available for every tree, including zero-capacity trees. This is the guard used by Theorem 21; the later results can also use it.
--
--   **Formalization Note** The exact source constant is retained. Unary nodes, extra leaves and arbitrary depth are permitted. The root has no parent edge; its unused capacity does not affect $R_T$.
--
--   Differences from the source:
--   - encoding: the known capacitated hierarchy tree and deterministic construction with no G queries → a function of the capacitated rooted tree with childless terminals, and the all-shore 42 inequalities; reason: tree indexing and a dummy root capacity preserve every instance; no oracle argument permits any query
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 26, printed p.29 (PDF p.30); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Hierarchies

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem terminal_guard (n : ℕ) (hn : 2 ≤ n) :
    ∃ guard : CapacitatedTree n → ExplicitGraph n,
      ∀ T, (∀ v u, u ≠ T.tree.root → T.tree.parent u ≠ T.terminal v) →
        TerminalGuard T (guard T) := by sorry

end LeeCutCertificates.Certificate.Supplement
