-- Prove2me | Theorems.Thm_HScattered_Delsarte_theorem_3_3
-- name    : HScattered.Delsarte.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:12.560904+00:00
-- url     : https://prove2.me/theorems/c1e68232-0bc6-416f-9f9c-641931607cd4
-- title:
--   Theorem 3.3 — for n ≥ h + 3 the Delsarte dual of a maximum h-scattered subspace of dimension rn/(h + 1) is maximum (n − h − 2)-scattered
-- statement:
--   Work in the setting of §3: $\mathbb V=\Lambda\oplus\Gamma$ is a $k$-dimensional $\mathbb F_{q^n}$-vector space with $\Lambda=V(r,q^n)$, $W$ is a $k$-dimensional $\mathbb F_q$-subspace of $\mathbb V$ with $\langle W\rangle_{\mathbb F_{q^n}}=\mathbb V$ and $W\cap\Gamma=\{0\}$, $U=\langle W,\Gamma\rangle_{\mathbb F_q}\cap\Lambda$, and $\beta$ is a non-degenerate reflexive sesquilinear form on $\mathbb V$ taking $\mathbb F_q$-values on $W\times W$, with orthogonal complement map $\perp$.
--
--   Suppose that $U$ is a maximum $h$-scattered $\mathbb F_q$-subspace of $\Lambda$ of dimension $rn/(h+1)$, and that $n\ge h+3$. Then the Delsarte dual $\bar U=W+\Gamma^\perp$ satisfies:
--
--   1. $\bar U$ is a **maximum $(n-h-2)$-scattered** $\mathbb F_q$-subspace of $\mathbb V/\Gamma^\perp$;
--   2. $\dim_{\mathbb F_q}\bar U=k$;
--   3. $\mathbb V/\Gamma^\perp=V\!\left(\tfrac{rn}{h+1}-r,\,q^n\right)$, that is,
--
--   $$
--   \dim_{\mathbb F_{q^n}}\big(\mathbb V/\Gamma^\perp\big)+r=k=\dim_{\mathbb F_{q^n}}\mathbb V .
--   $$
--
--   Since every admissible choice of the embedding and of the form is allowed, the statement covers the Delsarte dual "obtained by the procedure of Proposition 3.1" whatever choices the procedure makes. The theorem converts maximum $h$-scattered subspaces of $V(r,q^n)$ of dimension $rn/(h+1)$ into maximum $(n-h-2)$-scattered subspaces of a space of different dimension, which the paper uses to construct maximum scattered subspaces when $h+1$ does not divide $r$.
--
--   **Formalization Note** $r$ and $n$ are bound by `hr : finrank K Λ = r` and `hn : finrank F K = n`; "of dimension $rn/(h+1)$" is $(h+1)\dim_{\mathbb F_q}U=rn$. "Maximum $h$-scattered in $\Lambda$" is Definition 1.1 applied to the ambient space `↥Λ`, so it includes $0<h<r$ and $\langle U\rangle_{\mathbb F_{q^n}}=\Lambda$. The index $n-h-2$ is natural-number subtraction, exact because $n\ge h+3$; Definition 1.1 in $\mathbb V/\Gamma^\perp$ then requires $0<n-h-2<k-r$, which is part of the conclusion. The paper's $k>r$ is not assumed: it follows from $n\ge h+3$ (p. 10). The non-degeneracy of $\beta$ and its $\mathbb F_q$-values on $W$ are hypotheses of the setting; without them $\bar U$ would not be the paper's Delsarte dual.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 9, Theorem 3.3 (proof pp. 9–10)

import Mathlib
import Definitions.Def_HScattered_Delsarte_IsHScattered
import Definitions.Def_HScattered_Delsarte_DelsarteSetting

namespace HScattered.Delsarte

/-- Theorem 3.3 (arXiv:1906.10590v2, p. 9): in the setting of §3, let `U = ⟨W, Γ⟩_{𝔽_q} ∩ Λ` be a
maximum h-scattered `𝔽_q`-subspace of `Λ = V(r, qⁿ)` of dimension `rn/(h + 1)`, with `n ≥ h + 3`.
Then its Delsarte dual `Ū = W + Γ^⊥` is a maximum `(n − h − 2)`-scattered `𝔽_q`-subspace of
`𝕍 / Γ^⊥`; moreover `Ū` has dimension `k = dim 𝕍 = rn/(h + 1)` and `𝕍 / Γ^⊥` has dimension
`rn/(h + 1) − r` (stated as `dim (𝕍 / Γ^⊥) + r = k`). -/
theorem theorem_3_3 {F K 𝕍 : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup 𝕍] [Module K 𝕍] [Module F 𝕍] [IsScalarTower F K 𝕍]
    [Fintype F] [Fintype K] [FiniteDimensional K 𝕍]
    (D : DelsarteSetting F K 𝕍) (h r n : ℕ)
    (hr : Module.finrank K D.Λ = r) (hn : Module.finrank F K = n)
    (hU : IsMaximumHScattered F K h D.U)
    (hdim : (h + 1) * Module.finrank F D.U = r * n)
    (hnh : h + 3 ≤ n) :
    IsMaximumHScattered F K (n - h - 2) D.dual ∧
      Module.finrank F D.dual = Module.finrank K 𝕍 ∧
      Module.finrank K (𝕍 ⧸ D.orth D.Γ) + r = Module.finrank K 𝕍 := by sorry

end HScattered.Delsarte
