-- Prove2me | Theorems.Thm_HSElemKernel_phiF_width
-- name    : HSElemKernel.phiF_width
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:28:17.534699+00:00
-- url     : https://prove2.me/theorems/97846d2a-1948-4404-bf2e-babfbbf272e1
-- title:
--   Section 4.3 — every clause of $\Phi_{\mathcal F}$ has width at most $d$
-- statement:
--   Let $d \ge 3$, $(U, \mathcal S, k)$ an instance of $d$-Hitting Set, $X \subseteq U$, $\mathcal F$ a two-level hash pair, $\gamma : U \to \{0,1\}^\ell$, and $E$ a cardinality encoder meeting Lemma 3.2's guarantee. Then every clause of $\Phi_{\mathcal F}$ has width at most $d$:
--   $$|C| \le d \quad\text{for every clause } C \text{ of } \Phi_{\mathcal F}.$$
--
--   The cardinality encodings and the definitions (7), (8) have clauses of width at most three, and each clause of the expansion of $F_{A,\rho}$ takes one literal per element of $A$. So $\Phi_{\mathcal F}$ is a $d$-CNF formula and the variable-pair reduction returns an instance of $d$-Hitting Set.
--
--   Differences from the source:
--   - generalization: X the union of a maximal packing, satisfying (1), and the encoder of Lemma 3.2 → any X ⊆ U and any encoder meeting Lemma 3.2's guarantee; any ℓ and γ; reason: the width bound uses only |A ∩ X| + |A ∩ W| = |A| ≤ d and width ≤ 3 of the encodings; it specializes to the paper's Φ_F
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 4.3, width of Φ_F, p.12

import Mathlib
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_HSElemKernel_phiF

namespace HSElemKernel

/-- **Section 4.3, width of `Φ_F`** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 4.3, p.12): "Since `d ≥ 3`, every clause of
`Φ_F` has width at most `d`."

For `d ≥ 3`, every cardinality encoder meeting Lemma 3.2's guarantee, every `d`-Hitting Set
instance, every `X ⊆ U`, pair `F` and address map `γ`, every clause of `phiF` has at most
`d` literals.

**Formalization Note** The page's `X` comes from a maximal packing; the statement holds for
every `X`. -/
theorem phiF_width (d : ℕ) (hd : 3 ≤ d) (E : CardEncoder) (CE : ℕ) (hE : E.Spec CE)
    (I : HSInstance) (hI : IsDHS d I) (X : Finset (Fin I.n)) (F : TwoLevelHash (Fin I.n))
    {ℓ : ℕ} (γ : Fin I.n → Fin ℓ → Bool) :
    ∀ cl ∈ phiF E I.S I.k X F γ, cl.length ≤ d := by sorry

end HSElemKernel
