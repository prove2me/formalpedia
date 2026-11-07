-- Prove2me | Theorems.Thm_LiftSAParity_semantic_subsumes_syntactic
-- name    : LiftSAParity.semantic_subsumes_syntactic
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:34.593371+00:00
-- url     : https://prove2.me/theorems/bb239cb4-1e66-40d6-9362-13aadf23e995
-- title:
--   §3 — semantic SA(⊕) subsumes SA(⊕) with coefficient size at most tripled
-- statement:
--   Let $\varphi$ be a CNF formula over a finite set of variables. Every SA(⊕) refutation $\pi$ of $\varphi$ yields a semantic SA(⊕) refutation $\pi'$ of $\varphi$ with
--   $$\text{coefficient size}(\pi')\le 3\cdot\text{coefficient size}(\pi).$$
--
--   This is the precise sense of the paper's remark that its lower bounds "actually hold for a stronger, semantic system": the Boolean axioms lie in $I_S$, and modulo $I_S$ each parity axiom $D_{I,J}$ equals $x_Ic_J+x_Jc_I-x_{I\triangle J}c_I$, a combination of complementarity axioms with three times the coefficient size. It transfers the semantic lower bound of Lemma 3.4 to SA(⊕).
--
--   Differences from the source:
--   - reading: "Our lower bounds actually hold for a stronger, semantic system" (no transfer statement) → every SA(⊕) refutation gives a semantic one of at most 3 times the coefficient size; reason: the paper gives no explicit transfer; this is the coefficient-size form of the remark, with the factor of the rewriting of D_{I,J} modulo I_S
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §3, p.9

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_SemSAXorRefutation
import Definitions.Def_LiftSAParity_SAXorRefutation

namespace LiftSAParity

/-- **Semantic SA(⊕) subsumes SA(⊕)** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §3, p.9: "Our lower bounds actually hold for a
stronger, semantic system which we define next."): every SA(⊕) refutation `π` of a CNF formula
`φ` yields a semantic SA(⊕) refutation `π'` of `φ` with coefficient size at most `3` times that
of `π`.

**Formalization Note** The paper does not state the factor; `3` is the factor of the rewriting
`D_{I,J} ≡ x_I c_J + x_J c_I − x_{I△J} c_I (mod I_S)` together with `B_n ⊆ I_S`. -/
theorem semantic_subsumes_syntactic {V : Type*} [Fintype V] [DecidableEq V] (φ : CNF V)
    (π : SAXorRefutation φ) : ∃ π' : SemSAXorRefutation φ, π'.coeffSize ≤ 3 * π.coeffSize := by sorry

end LiftSAParity
