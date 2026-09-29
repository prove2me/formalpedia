-- Prove2me | Theorems.Thm_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace
-- name    : NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/8ee9bd7f-cc59-5643-b54b-89c73ba286d6
-- title:
--   Finite-adelic trace is the sum of local traces above p
-- statement:
--   Let $K$ be a number field, let $x$ be a finite adele of $K$, i.e. an element of `FiniteAdeleRing (𝓞 K) K`, and let $p$ be a height-one prime of $\mathbb{Z} = \mathcal{O}_{\mathbb{Q}}$. The primes $w$ of $\mathcal{O}_K$ lying over $p$, that is the elements of `p.Extension (𝓞 K)`, the subtype of height-one primes $w$ of $\mathcal{O}_K$ with $w \cap \mathcal{O}_{\mathbb{Q}} = p$, form a finite set, and the finiteness used to form the sum is the one furnished by `HeightOneSpectrum.Extension.fintype`. The assertion is that the component at $p$ of the finite-adelic trace `traceFinHom K x` equals $\sum_{w \mid p} \mathrm{Tr}_{K_w/\mathbb{Q}_p}(x_w)$, where for each such $w$ the summand is `Algebra.trace` of the extension of completions `p.adicCompletion ℚ` $\to$ `w.adicCompletion K` applied to the $w$-component $x_w$ of $x$. Here `traceFinHom K` is the additive map $\mathbb{A}_K^{f} \to \mathbb{A}_{\mathbb{Q}}^{f}$ defined by choosing, for a given $x$, an element $k \in K$ whose diagonal image added to $x$ has all components in the local integers, applying the integral trace map `traceInt K` (the continuous extension, along the dense image of $\mathcal{O}_K$, of $a \mapsto \mathrm{Tr}_{\mathcal{O}_K/\mathbb{Z}}(a)$) to that integral adele, and subtracting the diagonal image of $\mathrm{Tr}_{K/\mathbb{Q}}(k)$.
--
--   This is the local–global decomposition of the trace, $\mathrm{Tr}_{K/\mathbb{Q}} = \sum_{w \mid p} \mathrm{Tr}_{K_w/\mathbb{Q}_p}$, transported to finite adeles: it identifies the componentwise behaviour of the adelic trace map, which is otherwise defined by continuous extension from the integral adeles together with a translation by an element of $K$. It is used in the construction of the standard additive character, in [`NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace`](thm.html#NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace), which compares the local character of $K_w$ with the local character of $\mathbb{Q}_p$ composed with the local trace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.StandardAddChar

theorem NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace
    (K : Type) [Field K] [NumberField K]
    (x : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    (traceFinHom K x) p
      = ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) (x w.1) := by sorry
