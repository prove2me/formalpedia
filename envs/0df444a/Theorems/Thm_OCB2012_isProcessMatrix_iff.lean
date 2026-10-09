-- Prove2me | Theorems.Thm_OCB2012_isProcessMatrix_iff
-- name    : OCB2012.isProcessMatrix_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T09:44:22.954959+00:00
-- url     : https://prove2.me/theorems/5720bbdf-13fa-4338-aba6-e44fe7b2a5b6
-- title:
--   Eqs. (4)–(5) + App. C: $W$ is a process matrix iff $W\ge0$, $\mathrm{Tr}W = d_{A_2}d_{B_2}$, and $W$ has only allowed Hilbert–Schmidt terms
-- statement:
--   Fix Hilbert–Schmidt bases $\{\sigma_\mu\}$ of the operators on $A_1, A_2, B_1, B_2$, with $\sigma_0 = \mathbb 1$, the other elements Hermitian and traceless, and $\mathrm{Tr}\,\sigma_\mu\sigma_\nu = d\,\delta_{\mu\nu}$. A matrix $W$ on $A_1A_2B_1B_2$ is a process matrix, meaning it satisfies (4) $W\ge0$ and (5) $\mathrm{Tr}[W(M^{A_1A_2}\otimes M^{B_1B_2})] = 1$ for all CJ matrices of CPTP maps, if and only if
--
--   1. $W\ge0$;
--   2. $\mathrm{Tr}\,W = d_{A_2}d_{B_2}$;
--   3. $\mathrm{Tr}[W(\sigma_\mu^{A_1}\otimes\sigma_\nu^{A_2}\otimes\sigma_\lambda^{B_1}\otimes\sigma_\gamma^{B_2})] = 0$ for every term of a type not allowed in Fig. 3. These are the types $A_2$, $B_2$, $A_1A_2$, $B_1B_2$, $A_2B_2$, $A_1A_2B_2$, $A_2B_1B_2$ and $A_1A_2B_1B_2$.
--
--   This packages the paper's conclusion of Appendix C, that the most general matrix satisfying (5) is $W = \frac{1}{d_{A_1}d_{B_1}}(\mathbb 1+\sigma^{B\not\preceq A}+\sigma^{A\not\preceq B}+\sigma^{A\not\preceq\not\succeq B})$, together with positivity (4). The result is a complete, checkable description of the set of bipartite process matrices.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Eqs. (4)-(5) (p. 4) and Appendix C (p. 9, final display: the most general matrix satisfying (5))

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem isProcessMatrix_iff {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (BA1 : HSBasis a1) (BA2 : HSBasis a2) (BB1 : HSBasis b1) (BB2 : HSBasis b2)
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) :
    IsProcessMatrix W ↔
      (W.PosSemidef ∧ W.trace = (Fintype.card a2 * Fintype.card b2 : ℂ) ∧
        ∀ μ ν l γ, ¬ AllowedType μ.isSome ν.isSome l.isSome γ.isSome →
          (W * ((BA1.σ μ ⊗ₖ BA2.σ ν) ⊗ₖ (BB1.σ l ⊗ₖ BB2.σ γ))).trace = 0) := by sorry

end OCB2012
