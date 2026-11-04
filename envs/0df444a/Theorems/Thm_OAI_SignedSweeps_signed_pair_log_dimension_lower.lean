-- Prove2me | Theorems.Thm_OAI_SignedSweeps_signed_pair_log_dimension_lower
-- name    : OAI.SignedSweeps.signed_pair_log_dimension_lower
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T00:09:29.685251+00:00
-- url     : https://prove2.me/theorems/b8309bde-1a0d-4a96-b339-ca16dbd7775b
-- title:
--   Entropy lower bound for the dimension of a constituent of a signed type
-- statement:
--   This is the dimension lower bound for the constituents of a signed type: a Specht module containing $S^a\otimes S^{b^t}$ has dimension at least the exponential of the entropy of $(a,b)$, up to a polynomial factor controlled by the number of rows.
--
--   Let $u+v=n$, let $a\vdash u$ and $b\vdash v$ have at most $q$ rows each, and let $\lambda\vdash n$. Fix a bijection $e:\{1,\dots,u\}\sqcup\{1,\dots,v\}\to\{1,\dots,n\}$, which embeds $S_u\times S_v$ in $S_n$, and suppose there is an injective linear map $S^a\otimes S^{b^t}\to S^\lambda$ intertwining $S_u\times S_v$. Write
--
--   $$
--   F(a,b)=\sum_{x\in a\cup b}x\log\frac{u+v}{x}
--   $$
--
--   for the entropy of the concatenated row lengths. Then for every integer $B\ge 2n+2q+1$,
--
--   $$
--   F(a,b)-4q\big(\log(n+1)+1\big)-12q^2\log B\le\log\dim S^\lambda.
--   $$
--
--   This compares the dimension of a constituent with the entropy of the type, and it is the input that turns a moment bound into a saving of the entropy in the local stabilizer traces.
--
--   **Formalization Note** The Lean statement fixes an explicit occurrence through the map $f$ rather than the induced module, and its explicit constants differ from those displayed in Lemma 3.4 of the source. It is reproduced verbatim from `SignedPairDimension.lean`.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 3, Lemma 3.4, eq. (14). Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/SignedPairDimension.lean#L133-L168

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

theorem signed_pair_log_dimension_lower {u v n q : ℕ}
    (hn : u+v=n) (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x))
    (B : ℕ) (hB : 2*n+2*q+1 ≤ B) :
    signedEntropy a b - 4*(q : ℝ)*(Real.log (n+1 : ℕ)+1) -
      12*(q : ℝ)^2*Real.log B ≤ Real.log (spechtDimension lam : ℝ) := by sorry

end SignedSweeps
end
end OAI
