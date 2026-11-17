-- Prove2me | Theorems.Thm_MultitaskContracts_Supplement_theorem_3
-- name    : MultitaskContracts.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:07:31.684484+00:00
-- url     : https://prove2.me/theorems/ab7c2f2e-d177-4479-9a1f-68757f21ada1
-- title:
--   Theorem 3 — beyond independence, $\mathrm{PoSep}_{\mathrm{MinPay}}=\infty$ already for two identical MMLRP tasks with modular $f$
-- statement:
--   Let $K$ be a set of two tasks. Consider the class of instances on $K$ whose tasks are **identical** (equal $c,p,q$, and a joint distribution invariant under permuting the tasks, eq. (9)), which satisfy the **Multivariate Monotone Likelihood Ratio Property** (eq. (2)), and whose full-success probability $f(S)=P_S(K)$ is **modular**, $f(A)+f(B)=f(A\cup B)+f(A\cap B)$, hence both submodular and supermodular. Over this class, the price of separation of Min-Pay (Definition 1) is infinite:
--   $$\mathrm{PoSep}_{\mathrm{MinPay}}\;=\;\sup_{I}\frac{\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinPay}}(I)}{\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}(I)}\;=\;\infty.$$
--   Independence is not assumed. In particular, beyond independence the price of separation of Min-Pay is unbounded, in contrast with the value $|K|$ under independence (Theorem 2).
--
--   **Formalization Note** The price of separation is the published supremum in $[0,\infty]$ with the convention $\infty/\infty:=1$. The class is a subclass of all instances on two tasks, so the statement also gives $\mathrm{PoSep}_{\mathrm{MinPay}}=\infty$ over all of them.
--
--   Differences from the source:
--   - encoding: PoSep_MinPay = ∞ beyond independence, even for two identical tasks under MMLRP with a modular f → for every K with Fintype.card K = 2, priceOfSeparation of optMinPay over {I | I.IsIdentical ∧ I.MMLRP ∧ IsModularF I} = ⊤; reason: "even for" names the class over which the supremum is taken; a supremum over a superclass is then ⊤ as well
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Theorem 3, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_separable
import Definitions.Def_MultitaskContracts_priceOfSeparation
import Definitions.Def_MultitaskContracts_Instance_IsIdentical
import Definitions.Def_MultitaskContracts_Instance_MMLRP
import Definitions.Def_MultitaskContracts_Supplement_IsModularF

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

/-- **Theorem 3** (§4.2.3, p.26, PDF 28). Beyond independence, `PoSep_MinPay = ∞`, even for two
identical tasks under MMLRP with a modular, hence both submodular and supermodular, `f`: for every
set `K` of two tasks, the price of separation of Min-Pay over the instances on `K` with identical
tasks (published `Instance.IsIdentical`), MMLRP (published `Instance.MMLRP`) and a modular
full-success probability `f(S) = P_S(K)` (`IsModularF`) is `∞`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Theorem 3, p.26.

**Formalization Note.** `PoSep` is the published `priceOfSeparation` (Definition 1, supremum in
`ℝ≥0∞`, `∞/∞ := 1`) for the objective `OPT_MinPay`. Independence is not assumed. Since the class
is a subclass of all instances on `K`, the statement also gives `PoSep_MinPay = ∞` over all
instances on two tasks. -/
theorem theorem_3 (K : Type*) [Fintype K] [DecidableEq K] (hK : Fintype.card K = 2) :
    priceOfSeparation (fun I T => I.optMinPay T)
      {I : Instance K | I.IsIdentical ∧ I.MMLRP ∧ IsModularF I} = ⊤ := by sorry

end MultitaskContracts.Supplement
