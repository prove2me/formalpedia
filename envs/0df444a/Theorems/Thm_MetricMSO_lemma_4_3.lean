-- Prove2me | Theorems.Thm_MetricMSO_lemma_4_3
-- name    : MetricMSO.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:40.413379+00:00
-- url     : https://prove2.me/theorems/df6838e9-3013-453d-beca-d87481169dd2
-- title:
--   Lemma 4.3 — the translation $\sigma_M$ preserves satisfaction, in polynomial length
-- statement:
--   Let $M\ge3$ and let $\varphi$ be a $\mathrm{CMSO}_2[\mathsf{SP},\mathsf{EqGC}]$ formula. Then:
--
--   1. $\sigma_M(\varphi)$ is a $\mathrm{CMSO}_2$ formula, and a $\mathrm{CMSO}_1$ formula when $\varphi$ is in $\mathrm{CMSO}_1[\mathsf{SP},\mathsf{EqGC}]$;
--   2. there is a fixed polynomial $q$ such that $|\sigma_M(\varphi)|\le q(|\varphi|+M)$;
--   3. on every graph with $\mathrm{cbl}(G)<M$ and for every assignment $\alpha$ of the free variables,
--   $$G,\alpha\models\varphi\iff G,\alpha\models\sigma_M(\varphi).$$
--
--   **Formalization Note** `sigma M φ dV dS` is read in a context of `dV` vertex and `dS` vertex-set variables, and the assignment fills exactly this context. The polynomial is $c\,(\cdot+1)^c$.
--
--   Differences from the source:
--   - encoding: |σ_M(φ)| ≤ q(|φ| + M) → (sigma M φ dV dS).length ≤ c(|φ| + M + dV + dS + 1)^c; reason: when the context holds exactly the free variables of φ, dV + dS ≤ |φ|, which gives the page's form; bound variables are levels above the context, so the context size enters the code
--   - generalization: assignments of the free variables of φ → every assignment filling a context of dV vertex and dS vertex-set variables, also with an atom out of scope, which is false on both sides; reason: it specializes to the source when the context is the set of free variables
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Lemma 4.3 and the paragraph after it, p.28 (PDF 30)

import Mathlib
import Definitions.Def_MetricMSO_Sat
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_IsCMSO1
import Definitions.Def_MetricMSO_sigma

namespace MetricMSO

/-- **Lemma 4.3.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.28 (PDF 30): "Let G be a graph and let M ≥ 3
satisfy M > cbl(G). For every CMSO1[SP, EqGC] formula φ and every assignment α of its free variables,
we have G, α |= φ if and only if G, α |= σM(φ). Moreover, there is a fixed polynomial q such that
|σM(φ)| ≤ q(|φ| + M). For incidence structures, we again restrict the auxiliary element variables to
vertices and the auxiliary set variables to subsets of V(G). The same statements then hold for the
translation from CMSO2[SP, EqGC] to CMSO2."

**Formalization Note** Every `Formula` is a CMSO2[SP, EqGC] formula, so the statement for all `φ` is the
CMSO2 case. `σ_M` is `sigma M φ dV dS`, read in a context of `dV` vertex and `dS` vertex-set variables,
which is also the shape of an assignment `ρ` of them (edge and edge-set variables are unconstrained).
The translation lands in CMSO2 (`NoMetric`), and in CMSO1 when `φ` is a CMSO1 formula. The polynomial
`q` is `c · (· + 1)^c`, with the context size added to its argument: when the context holds exactly the
free variables of `φ`, then `dV + dS ≤ |φ|`, which gives the page's `q(|φ| + M)` form. -/
theorem lemma_4_3 :
    ∃ c : ℕ, ∀ M : ℕ, 3 ≤ M → ∀ (φ : Formula) (dV dS : ℕ),
      NoMetric (sigma M φ dV dS) ∧
      (IsCMSO1 φ → IsCMSO1 (sigma M φ dV dS)) ∧
      (sigma M φ dV dS).length ≤ c * (φ.length + M + dV + dS + 1) ^ c ∧
      ∀ I : Instance, cbl I.G < M → ∀ ρ : Env I.n, ρ.v.length = dV → ρ.s.length = dS →
        (Sat I ρ φ ↔ Sat I ρ (sigma M φ dV dS)) := by sorry

end MetricMSO
