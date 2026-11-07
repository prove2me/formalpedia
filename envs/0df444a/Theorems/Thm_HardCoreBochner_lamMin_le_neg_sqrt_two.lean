-- Prove2me | Theorems.Thm_HardCoreBochner_lamMin_le_neg_sqrt_two
-- name    : HardCoreBochner.lamMin_le_neg_sqrt_two
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:30.833954+00:00
-- url     : https://prove2.me/theorems/b70e6521-5457-4e08-a768-4c9ab5187afc
-- title:
--   Auxiliary — $\lambda_{\min}(A_G)<-1$ implies $\lambda_{\min}(A_G)\le-\sqrt2$
-- statement:
--   This lemma is not stated in the paper. Let $G$ be a finite simple graph. If $\lambda_{\min}(A_G)<-1$, then
--   $$\lambda_{\min}(A_G)\le-\sqrt2 .$$
--   It supplies the bound on $\lambda$ that the final step of the proof of Theorem 1.1, "Bounding $\log(1/\mu_{\min})\le O(n\log(1+1/\lambda))$" (p.4), needs: under $\lambda\le(1-\delta)/(-\lambda_{\min}(A_G)-1)$ it gives $\lambda<1/(\sqrt2-1)=1+\sqrt2$. The bound on $\log(1/\mu_{\min})$ fails for unbounded $\lambda$, so the theorem depends on it.
--
--   Differences from the source: none.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), auxiliary to the proof of Theorem 1.1, p.4 (PDF p.4), step 'Bounding log(1/µmin) ≤ O(n log(1 + 1/λ))'

import Definitions.Def_HardCoreBochner_lamMin

namespace HardCoreBochner

/-- **Auxiliary lemma (not stated in the paper).** If `λ_min(A_G) < −1` then `λ_min(A_G) ≤ −√2`.

It supplies the bound on `λ` that the step "Bounding log(1/µmin) ≤ O(n log(1 + 1/λ))" (Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), proof
of Theorem 1.1, p.4) needs: under `λ ≤ (1 − δ)/(−λ_min(A_G) − 1)` it gives `λ < 1/(√2 − 1) = 1 + √2`.

**Formalization Note** A graph with `λ_min(A_G) < −1` is not a disjoint union of cliques (those have
`λ_min ∈ {0, −1}`), so it contains an induced path on three vertices, whose adjacency matrix has
minimum eigenvalue `−√2`. -/
theorem lamMin_le_neg_sqrt_two {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : lamMin G < -1) : lamMin G ≤ -Real.sqrt 2 := by sorry

end HardCoreBochner
