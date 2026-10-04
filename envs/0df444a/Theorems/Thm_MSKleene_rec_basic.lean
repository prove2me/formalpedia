-- Prove2me | Theorems.Thm_MSKleene_rec_basic
-- name    : MSKleene.rec_basic
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:31:41.09549+00:00
-- url     : https://prove2.me/theorems/27099720-46ab-42fe-b503-388a2c47d258
-- title:
--   Proposition 3.29: basic terms are recognizable
-- statement:
--   **Basic terms are recognizable** (Proposition 3.29).
--
--   Assume $S$ finite. For every $s\in S$: (1) for every $x\in X_{s}$, $\{x\}$ is $s$-recognizable; (2) for every $\sigma\in\Sigma_{\lambda,s}$, $\{\sigma^{\mathbf{T}_{\Sigma}(X)}\}$ is $s$-recognizable; (3) for every $\mathbf{s}\in S^{\star}-\{\lambda\}$, $\sigma\in\Sigma_{\mathbf{s},s}$, and $(x_{j})_{j}\in X_{\mathbf{s}}$, $\{\sigma^{\mathbf{T}_{\Sigma}(X)}((x_{j})_{j})\}$ is $s$-recognizable. (From CVCL20, Prop. 3.1–3.3.)
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Term
import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Power

namespace MSKleene

/-- **Basic terms are recognizable** (Proposition 3.29; from CVCL20).

With `S` finite: for every sort `s`, every singleton `{x}` of a variable, and
every singleton `{σ(x₁,…,x_k)}` of an operation symbol applied to variables
(the constant case `k = 0` included), is `s`-recognizable. -/
theorem rec_basic {S : Type} [Finite S] (sig : Signature S) (X : SSet S) (s : S) :
    (∀ x : X s, sRecognizable (freeAlgebra sig X) s {Term.var x})
  ∧ (∀ (w : List S) (σ : sig w s) (xs : Args X w),
        sRecognizable (freeAlgebra sig X) s
          {Term.app σ (TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs))}) := by
  sorry

end MSKleene
