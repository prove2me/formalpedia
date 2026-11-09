-- Prove2me | Theorems.Thm_HSElemKernel_lemma_4_4
-- name    : HSElemKernel.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:28:09.378165+00:00
-- url     : https://prove2.me/theorems/2273cfc4-2d62-4774-9c75-d14bfb8c78bc
-- title:
--   Lemma 4.4 — $\Phi_{\mathcal F}$ is satisfiable iff a hitting set $Z$ with $|Z| \le k$ has $Z \cap W$ separated by $\mathcal F$
-- statement:
--   Let $(U, \mathcal S, k)$ be an instance, $X \subseteq U$ and $W = U \setminus X$, $\mathcal F$ a two-level hash pair, $\gamma : U \to \{0,1\}^\ell$ injective on $W$, and $E$ a cardinality encoder meeting Lemma 3.2's guarantee. Then
--   $$\Phi_{\mathcal F} \text{ is satisfiable} \iff \exists Z \subseteq U:\ |Z| \le k,\ Z \cap A \ne \emptyset \ \ \forall A \in \mathcal S,\ \text{and } \mathcal F \text{ separates } Z \cap W .$$
--
--   With Lemma 4.2 this gives the one-sided error of the randomized encoding: a NO-instance always yields an unsatisfiable formula, and a YES-instance yields a satisfiable one whenever $\mathcal F$ separates the hashed part of a fixed solution.
--
--   Differences from the source:
--   - generalization: X the union of a maximal packing, W = U \ X, the encoder of Lemma 3.2, ℓ = ⌈log₂(|W|+1)⌉ → any X ⊆ U, any encoder meeting Lemma 3.2's guarantee, any ℓ and γ injective on W; no size bound on the sets; reason: the proof uses only X ∩ W = ∅, distinct addresses and the encoder's correctness; it specializes to the paper's Φ_F
--   - encoding: F defined on W and Z ∩ W → F defined on all of U (only its values on W are read) and Z \ X; reason: same formula and same separation condition
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.4, p.13

import Mathlib
import Definitions.Def_HSElemKernel_HSInstance
import Definitions.Def_HSElemKernel_Separates
import Definitions.Def_HSElemKernel_phiF

namespace HSElemKernel

/-- **Lemma 4.4** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.4, p.13): the formula `Φ_F` is satisfiable iff there is a
hitting set `Z ⊆ U` of size at most `k` such that `F` separates `Z ∩ W`.

For every cardinality encoder `E` meeting Lemma 3.2's guarantee, every instance
`(Fin n, S, k)`, every `X ⊆ U` (with `W = U \ X`), pair `F` and address map `γ` injective
on `W`.

**Formalization Note** The page's `X` comes from a maximal packing and its encoder is the one
of Lemma 3.2; the statement holds for every `X` and every encoder with Lemma 3.2's guarantee.
`Z ∩ W` is `Z \ X`. -/
theorem lemma_4_4 (E : CardEncoder) (CE : ℕ) (hE : E.Spec CE) (I : HSInstance)
    (X : Finset (Fin I.n)) (F : TwoLevelHash (Fin I.n)) {ℓ : ℕ} (γ : Fin I.n → Fin ℓ → Bool)
    (hγ : Set.InjOn γ ((Xᶜ : Finset (Fin I.n)) : Set (Fin I.n))) :
    (∃ asg, (phiF E I.S I.k X F γ).eval asg = true) ↔
      ∃ Z : Finset (Fin I.n), Z.card ≤ I.k ∧ (∀ A ∈ I.S, (Z ∩ A).Nonempty) ∧
        Separates F (Z \ X) := by sorry

end HSElemKernel
