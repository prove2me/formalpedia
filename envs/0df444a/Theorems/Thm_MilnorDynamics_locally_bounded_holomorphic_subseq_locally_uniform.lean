-- Prove2me | Theorems.Thm_MilnorDynamics_locally_bounded_holomorphic_subseq_locally_uniform
-- name    : MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T18:38:01.031158+00:00
-- url     : https://prove2.me/theorems/9827712e-7fe5-48b9-9a4b-38487d1b6765
-- title:
--   Arzela-Ascoli extraction — a locally bounded holomorphic family has a locally uniformly convergent subsequence
-- statement:
--   **Arzel\`a\`{}-Ascoli extraction for holomorphic families.** Let $U\subseteq\mathbb C$ be open and let $f_n:U\to\mathbb C$ be holomorphic. Suppose the family $(f_n)$ is **locally bounded**: for every compact $K\subseteq U$ there is $M_K<\infty$ with $|f_n(z)|\le M_K$ for all $n$ and all $z\in K$. Then some subsequence $(f_{\varphi(n)})$ converges **locally uniformly** on $U$ to a continuous $g:U\to\mathbb C$; that is, for every compact $K_0\subseteq U$ and every $\varepsilon>0$ there is $N$ with $\sup_{z\in K_0}|f_{\varphi(n)}(z)-g(z)|<\varepsilon$ for all $n\ge N$.
--
--   **Why holomorphy is the right hypothesis.** The standard Arzel\`a\`{}-Ascoli theorem requires *equicontinuity*, which local boundedness alone does not give. For merely continuous maps the statement is false: on $\mathbb D$ take $f_n(z)=\max\{0,1-n|z|\}$. This is continuous, satisfies $|f_n|\le1$ so it is bounded on every compact, yet $f_n(0)=1$ for all $n$ while $f_n(z)\to0$ for every $z\neq0$. Any locally uniform limit would therefore take the value $1$ at $0$ and $0$ elsewhere, which is discontinuous, so no such limit exists. Holomorphy repairs this: Cauchy's derivative estimate on a slightly larger disk bounds $|f_n'|$ in terms of the local bound and the disk radius, giving the equicontinuity that Arzel\`a\`{}-Ascoli needs.
--
--   **Role in Montel's theorem.** This is the extraction step that lets one pass from a locally bounded family to a locally uniform limit, which is then fed to the Hurwitz dichotomy. It is the same extraction used twice in the proof of Milnor's Corollary 3.3: once on the family itself, and once on the reciprocals $1/f_n$ in the escape step.
--
--   **Formalization note** This corrects the previously published MilnorDynamics.locally_bounded_subseq_locally_uniform (theorem 5b631010-6dca-453f-8c87-809e48d9ae3f), which omitted the `DifferentiableOn` hypothesis and is therefore false; the bump family above refutes it.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, pp. 32-34: the 'the family is locally bounded, so some subsequence converges uniformly on compact subsets' step of Montel's theorem, used in the proof of Corollary 3.3. Arzela-Ascoli is formalised in Mathlib at Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean (BoundedContinuousFunction.arzela_ascoli) and Mathlib/Topology/UniformSpace/Ascoli.lean (ArzelaAscoli), with equicontinuity obtained from Cauchy's derivative estimate

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem locally_bounded_holomorphic_subseq_locally_uniform (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by sorry

end MilnorDynamics
