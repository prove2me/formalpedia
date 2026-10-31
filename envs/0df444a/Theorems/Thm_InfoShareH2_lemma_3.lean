-- Prove2me | Theorems.Thm_InfoShareH2_lemma_3
-- name    : InfoShareH2.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:55.993755+00:00
-- url     : https://prove2.me/theorems/26f611a2-308e-4d47-ad08-8321a22b6fdc
-- title:
--   Lemma 3 — removing the Blaschke factor keeps $\sigma_{S|NS}$ and lowers $\sigma_I$ (strictly unless $B\equiv1$)
-- statement:
--   Let $\sigma_\epsilon>0$ and let $\tilde\psi\in\tilde\Psi$ have the inner–outer factorization $\tilde\psi=QBG$ of Lemma 2. Let $\hat\psi=QG$, the function with the same outer and singular inner factors and no Blaschke factor, and let $(\hat\psi_n)$ be its Taylor coefficients. Then
--
--   $$\sigma^2_{S|NS}(\hat\psi)=\sigma^2_{S|NS}(\tilde\psi),\qquad \sigma^2_I(\hat\psi)\le\sigma^2_I(\tilde\psi),$$
--
--   and the inequality is strict unless $B\equiv1$.
--
--   Here $\sigma^2_I(\hat\psi)=\sigma_\epsilon^2\bigl(1+\sum_{n\ge1}|\sum_{k<n}\hat\psi_k-1|^2\bigr)\in[0,\infty]$ and $\sigma^2_{S|NS}(\hat\psi)$ is Kolmogorov's expression (26) for $\hat\psi$.
--
--   The lemma lets the proof of Theorem 2 discard all policies with zeros in the unit disk.
--
--   Differences from the source:
--   - reading: ψ̃ ∈ H² → ψ̃ ∈ Ψ̃ and σ_ε > 0; reason: Assumption 1 is standing from p.26
--   - reading: "the inner-outer factorization defined in (31)–(32)" → Lemma 2’s factorization: G with constant 1, the unimodular constant in B; reason: with a unimodular constant left in G the lemma fails (ψ̃ = 2z − 1, G ≡ −1 gives σ²_I(ψ̂) = ∞)
--   - reading: "strict unless B(z) ≡ 1" → if B is not identically 1 on D, then σ²_I(ψ̂) < σ²_I(ψ̃); reason: the printed clause
--   - encoding: σ²_I(ψ̂) and σ²_S|NS(ψ̂) for ψ̂ = QG → series (8) in [0, ∞] for complex coefficients (Taylor coefficients of QG); Kolmogorov expression with |ψ̂(e^{−iλ})|²; reason: ψ̂ is not known in advance to lie in Ψ̃; (8) equals (37) by Parseval
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Lemma 3, p.26 (proof §9.11, pp.46–47)

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Lemma 3 (suboptimality of Blaschke products).**
SSRN 4319721 (v. 2024-01-20), Lemma 3, p.26 (proof §9.11, pp.46–47). "Suppose `ψ̃ ∈ H²` has the
inner-outer factorization `ψ̃(z) = Q(z)B(z)G(z)` defined in (31)–(32). Let `ψ̂(z) = Q(z)G(z)`, then
we have `σ²_S|NS(ψ̂) = σ²_S|NS(ψ̃)` and `σ²_I(ψ̂) ≤ σ²_I(ψ̃)`. The inequality above is strict unless
`B(z) ≡ 1`."

**Formalization Note** Stated for `ψ̃ ∈ Ψ̃` (Assumption 1 standing from p.26) and `σ_ε > 0`, with
the factorization of Lemma 2 (constant `1` in `G`, unimodular constant in `B`). `ψ̂` is the sequence
of Taylor coefficients of `Q·G` at `0`. It is not known in advance to lie in `Ψ̃`, so `σ²_I` is
compared in `ℝ≥0∞` through `invVarE` (the series (8), possibly `∞`), and `σ²_S|NS(ψ̂)` is the
Kolmogorov expression `nsVarC` for a complex sequence. -/
theorem lemma_3 (σε : ℝ) (hσε : 0 < σε) (ψ : ℕ → ℝ) (hψ : ψ ∈ PsiTilde)
    (B : BlaschkeData) (G : SingularData) (hG : G.c = 1)
    (hfac : ∀ z ∈ Disk,
      zTransform (ofRealSeq ψ) z = outerPart (ofRealSeq ψ) z * B.eval z * G.eval z) :
    let hat : ℕ → ℂ := taylorCoeff (fun z => outerPart (ofRealSeq ψ) z * G.eval z)
    nsVarC σε hat = nsVar σε ψ ∧
    invVarE σε hat ≤ invVarE σε (ofRealSeq ψ) ∧
    ((¬ ∀ z ∈ Disk, B.eval z = 1) → invVarE σε hat < invVarE σε (ofRealSeq ψ)) := by sorry

end InfoShareH2
