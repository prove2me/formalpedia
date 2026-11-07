-- Prove2me | Theorems.Thm_HardCoreBochner_lemma_2_1
-- name    : HardCoreBochner.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:22.445784+00:00
-- url     : https://prove2.me/theorems/4a184946-0b3c-44aa-aafc-f7688c79649e
-- title:
--   Lemma 2.1 — integration by parts; $L$ is self-adjoint in $\ell^2(\mu)$
-- statement:
--   Let $\mu$ be a distribution fully supported on a non-empty downward-closed family $X\subseteq\{0,1\}^V$, with jump rates $r_v$ and generator $L$. For all $f,g:\{0,1\}^V\to\mathbb R$:
--
--   1. $$-\langle f,Lg\rangle_\mu=\sum_{v\in V}\mathbb E_\mu\big[r_v(\sigma)\,D^+_vf(\sigma)\,D^+_vg(\sigma)\big];\tag{10}$$
--   2. $\langle f,Lg\rangle_\mu=\langle Lf,g\rangle_\mu$, i.e. $L$ is self-adjoint with respect to $\langle\cdot,\cdot\rangle_\mu$.
--
--   The identity (10) expresses the Dirichlet form of $L$ through the discrete gradients and is used throughout §2.
--
--   Differences from the source:
--   - encoding: a distribution µ fully supported on a non-empty downward-closed family X ⊆ {0,1}^V → IsDownClosedLaw µ for µ : (V → Bool) → ℝ, with X := {σ | 0 < µ σ}; reason: the support of such a µ is exactly such an X, and every such pair (X, µ) arises this way; same instances
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), Lemma 2.1, (10), p.7 (PDF p.7)

import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_gen
import Definitions.Def_HardCoreBochner_ip

namespace HardCoreBochner

open scoped BigOperators

/-- **Lemma 2.1** (integration by parts). Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), Lemma 2.1, (10), p.7.

Let `µ` be a distribution fully supported on a non-empty downward-closed family `X ⊆ {0,1}^V`. For
all `f, g : {0,1}^V → ℝ`,
`−⟨f, Lg⟩_µ = Σ_{v∈V} E_µ[ r_v(σ) D⁺_v f(σ) D⁺_v g(σ) ]`, and in particular `L` is self-adjoint:
`⟨f, Lg⟩_µ = ⟨Lf, g⟩_µ`.

**Formalization Note** `X` is the support of `µ` (`IsDownClosedLaw`); both clauses are stated. -/
theorem lemma_2_1 {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (hμ : IsDownClosedLaw μ) (f g : (V → Bool) → ℝ) :
    -ip μ f (gen μ g) = ∑ v, expect μ (fun σ => rate μ v σ * Dplus v f σ * Dplus v g σ) ∧
      ip μ f (gen μ g) = ip μ (gen μ f) g := by sorry

end HardCoreBochner
