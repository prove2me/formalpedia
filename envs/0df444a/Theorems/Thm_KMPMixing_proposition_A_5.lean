-- Prove2me | Theorems.Thm_KMPMixing_proposition_A_5
-- name    : KMPMixing.proposition_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:27.777194+00:00
-- url     : https://prove2.me/theorems/c60512ed-5d99-4089-ae17-6a8193acfe22
-- title:
--   Proposition A.5 — $\lambda_2(M^{(2,G)}_{\mathrm{LKMP}})=\max\{\lambda_2(M^{(2,G)}_{\mathrm{KMP}}),\lambda_1(C|_{\mathcal H_{\mathrm{Asym}}})\}$
-- statement:
--   Let $G=(V=[d],E)$ be a connected graph with $d\ge2$, and let $\lambda_1$, $\lambda_2$ denote the largest and second largest eigenvalue in absolute value. Then
--   $$
--   \lambda_2\big(M^{(2,G)}_{\mathrm{LKMP}}\big)=\max\Big\{\lambda_2\big(M^{(2,G)}_{\mathrm{KMP}}\big),\ \lambda_1\big(C|_{\mathcal H_{\mathrm{Asym}}}\big)\Big\}.
--   $$
--
--   The two-particle labeled chain splits into a symmetric block, which is the unlabeled two-particle chain, and an antisymmetric block, which is $C$.
--
--   Differences from the source:
--   - reading: "fix a graph $G$" (Appendix A) → $G$ connected with $d\ge2$; reason: the chains $M_{\mathrm{KMP}}$, $M_{\mathrm{LKMP}}$ are defined only on connected graphs (Definitions 3.1, 3.3), and with $d=1$ there is no edge
--   - encoding: $\lambda_2$ → `MarkovMixing.lambdaStar`; $\lambda_1(C|_{\mathcal H_{\mathrm{Asym}}})$ → the largest $|\lambda|$ over eigenvalues of $C$ with an antisymmetric eigenfunction; reason: eigenvalue $1$ is simple for these irreducible chains, and $\mathcal H_{\mathrm{Asym}}$ is $C$-invariant
-- source:
--   Chen et al., arXiv:2609.38044, Proposition A.5, p.66 (PDF p.68); standing assumption p.61

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
import Definitions.Def_KMPMixing_lambdaOneAsym
open MarkovMixing

namespace KMPMixing

/-- **Proposition A.5** (arXiv:2609.38044, p.66 (PDF p.68)). With `t = 2` and a fixed graph `G`,
`λ₂(M^{(2,G)}_LKMP) = max{λ₂(M^{(2,G)}_KMP), λ₁(C|_{𝓗_Asym})}`,
where `λ₁`, `λ₂` are the largest and second largest eigenvalues in absolute value.

**Formalization Note** `λ₂` is `MarkovMixing.lambdaStar` (largest `|λ|` over eigenvalues
`λ ≠ 1`; eigenvalue `1` is simple on these irreducible chains); `λ₁(C|_{𝓗_Asym})` is
`lambdaOneAsym G`. The labeled chain lives on `Fin 2 → Fin d`, the unlabeled one on `Δ_G` with
`t = 2`, and `C` on `Fin d × Fin d`. The standing assumption of Appendix A is a connected graph
on `d` vertices; `d ≥ 2` is added (a graph with an edge). -/
theorem proposition_A_5 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) :
    lambdaStar (labeledChain G 2) = max (lambdaStar (kmpChain G 2)) (lambdaOneAsym G) := by sorry

end KMPMixing
